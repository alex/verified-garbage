import VerifiedGarbage.Proof.Aes.X86.AesNi.Context
import VerifiedGarbage.Proof.Aes.X86.AesNi.Setup

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP datR scrR ctrR argR)
open VG.Spec.Gcm (blockAt inc32)

/-- After c encrypted blocks, public data/count registers point at block p.
The prefix and saved callee registers stay in scratch throughout both loops. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nBlk s₀
  ebx : s.gpr .ebx = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c
  esp : s.gpr .esp = s₀.gpr .esp
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  ebp : s.gpr .ebp = scrP s₀
  esi : s.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀ - p)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [datR s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 = (0 : BitVec 32) ++ pfx s₀
  blocks : ∀ k < nBlk s₀,
    blockAt s.mem (bAddr s₀ k) = if k < c then
      blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else blk s₀ k

/-- A subrange of the encrypted run lies in the public data region. -/
theorem run_in {s₀ : State} {c n : Nat} (hn : c + n ≤ nBlk s₀) :
    Region.Sub ⟨bAddr s₀ c, 16 * n⟩ (datR s₀) :=
  Offset.sub_base _ (by omega)

/-- A data block outside the encrypted run cannot overlap that run. -/
theorem run_sep {s₀ : State} (hp : CPre s₀) {c n k : Nat} (hk : k < nBlk s₀)
    (hn : c + n ≤ nBlk s₀) (hout : ¬ (c ≤ k ∧ k < c + n)) :
    Region.Disjoint ⟨bAddr s₀ k, 16⟩ ⟨bAddr s₀ c, 16 * n⟩ := by
  have hw := hp.fD
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- Entry setup supplies the loop invariant before any data is encrypted. -/
theorem Inv.of_start {s₀ s : State} (hp : CPre s₀) (hs : Start s₀ s) :
    Inv s₀ 0 0 s := by
  refine ⟨Nat.zero_le _, ?_, hs.esp, hs.ecx, hs.edx, hs.ebp, ?_, ?_, hs.rd, hs.wr,
    ?_, hs.saved, hs.scratchPrefix, ?_⟩
  · rw [hs.ebx, BitVec.add_zero]
  · rw [hs.esi, Nat.mul_zero, BitVec.add_zero]
  · simpa only [Nat.sub_zero] using hs.edi
  · exact hs.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩
  · intro k hk
    simp only [Nat.not_lt_zero, ite_false]
    exact blockAt_frame hs.frame (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.sub_left (run_in (s₀ := s₀) (c := k) (n := 1) (by omega)))

end VG.Proof.Aes.X86.AesNi
