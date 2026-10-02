import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame

/-! # H′: arguments for the caller's input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InputArgs (s t : State) : Prop where
  count : t.gpr .x1 = 4
  data : t.gpr .x2 = s.gpr .x20
  size : t.gpr .x3 = s.gpr .x21
  other : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (16 * 0 : Nat) < 64 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
  refine ⟨fun r hr _ => ?_, h.rd, h.wr, h.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbInput_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .x24) headBytes) (len : (s.gpr .x21).toNat < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩) :
    WP isa (absorbInput v.hash) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (headBytes ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) ∧
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .x24) headBytes := by rw [hu.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .x3).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .x2, (u.gpr .x3).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24, 192⟩ := by
    rw [hu.data, hu.size, ku.x24]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24 + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.x24]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  have sd : (below u.sp 16).Disjoint ⟨u.gpr .x2, (u.gpr .x3).toNat⟩ := by
    rw [hu.data, hu.size, ku.sp]; exact stackData
  refine (update_ok v u h0 headBytes repr' count bound (by rw [ku.sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', update_frame _ _ frame⟩⟩
  simpa only [ku.x24, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.AArch64.HPrime
