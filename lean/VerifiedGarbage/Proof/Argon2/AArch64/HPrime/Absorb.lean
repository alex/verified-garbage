import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Fixed
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame

/-! # H′: absorbing the length prefix or previous digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbFixed_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetUpper : offset < 4096)
    (hsp : 16 ≤ s.sp.toNat)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .x24) [])
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (absorbFixed v.hash offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (bytesAt s.mem (s.gpr .x24 + BitVec.ofNat 64 offset) size) ∧
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetUpper (by omega)).mono fun u hu => ?_)
  have p : u.gpr .x24 = s.gpr .x24 := hu.other _ (by decide) (by decide) (by decide)
  have sp := hu.sp
  have len : (u.gpr .x3).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .x24) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .x1 = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .x3).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega
  have cover : Covers [⟨u.gpr .x2, (u.gpr .x3).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .x3).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  have dw : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24 + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below u.sp 16).Disjoint ⟨u.gpr .x2, (u.gpr .x3).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (update_ok v u h0 [] hr hc hb (by rw [sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', sp', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr h30 => (regs r hr h30).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .x24) u.sp frame

end VG.Proof.Argon2.AArch64.HPrime
