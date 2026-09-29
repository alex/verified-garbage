import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa

/-!
# Calls of `vg_salsa20_8` on x86-64

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its `Verified` proof by `WP.call`.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64
open VG.Spec.Scrypt (bytesAt salsa)
open VG.Proof.Sha1.X86_64.Stream (callEntry_byte)

theorem salsa_depth : Impl.Scrypt.X86_64.salsa.depth = 0 := by decide +kernel

theorem salsa_nosp : NoSp Impl.Scrypt.X86_64.salsa := by
  have : ((instrs Impl.Scrypt.X86_64.salsa).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- A region inside one of `rs` is covered by `rs`. -/
theorem covers_of_in {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    Covers [⟨a, n⟩] rs := by
  obtain ⟨R, hR, hc⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨R, hR, (a - R.base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega, hc⟩

theorem covers_pair {rs : List Region} {a b : Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha x n ⟨_, List.mem_singleton_self _, hc⟩
  · exact hb x n ⟨_, List.mem_singleton_self _, hc⟩

theorem salsaSpec : SalsaSpec Impl.Scrypt.X86_64.salsa := by
  intro s d sc hd hsc hds hsd hss _ _ hind hins Q hQ
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Scrypt.salsaX86_64) salsa_correct salsa_nosp
    (by rw [salsa_depth]; decide) (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hd, hsc]
    exact ⟨trivial, trivial, hds, hsd, hss⟩
  · have := covers_pair (covers_of_in hind) (covers_of_in hins)
    intro a n h
    obtain ⟨R, hR, hc⟩ := this a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · exact covers_pair (covers_of_in hind) (covers_of_in hins)
  · intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
    simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hd, hm₃] at hpost
    rw [salsa_depth] at hf
    refine hQ s₂ hrd hwr hcs (by simpa using hf) ?_
    rw [hpost]
    congr 1
    exact bytesAt_congr fun i hi => callEntry_byte s (R := ⟨d, 64⟩) hsd (by simp) hi

end VG.Proof.Scrypt.X86_64.BlockMix
