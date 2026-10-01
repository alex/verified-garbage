import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Fixed
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame

/-! # H′: absorbing the length prefix or previous digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbFixed_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .rbx) [])
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (absorbFixed (hash v) offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 offset) size) ∧
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size (by omega) (by omega)).mono fun u hu => ?_)
  have p : u.gpr .rbx = s.gpr .rbx := hu.other _ (by decide) (by decide) (by decide)
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have len : (u.gpr .rcx).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .rbx) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .rsi = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .rcx).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega
  have cover : Covers [⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .rcx).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  have dw : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (update_ok v u h0 [] hr hc hb wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr => (regs r hr).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .rbx) (u.gpr .rsp) frame

end VG.Proof.Argon2.X86_64.HPrime
