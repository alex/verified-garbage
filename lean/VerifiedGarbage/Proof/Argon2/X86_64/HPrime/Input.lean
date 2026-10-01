import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame

/-! # H′: arguments for the caller's input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InputArgs (s t : State) : Prop where
  count : t.gpr .rsi = 4
  data : t.gpr .rdx = s.gpr .r12
  size : t.gpr .rcx = s.gpr .r13
  other : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbInput_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .rbx) headBytes) (len : (s.gpr .r13).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩) :
    WP isa (absorbInput (hash v)) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (headBytes ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) ∧
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .rbx) headBytes := by rw [hu.mem, ku.rbx]; exact repr
  have count : u.gpr .rsi = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .rcx).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ku.rbx, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx, 192⟩ := by
    rw [hu.data, hu.size, ku.rbx]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.rbx]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ku.rbx, ku.rsp]; exact stackWork
  have sd : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ := by
    rw [hu.data, hu.size, ku.rsp]; exact stackData
  refine (update_ok v u h0 headBytes repr' count bound wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', update_frame _ _ frame⟩⟩
  simpa only [ku.rbx, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.X86_64.HPrime
