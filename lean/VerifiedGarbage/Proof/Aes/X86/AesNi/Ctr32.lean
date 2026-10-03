import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk ctrSat)
open VG.Spec.Gcm (blockAt blocksAt)

/-- The invariant at exit is exactly the standard's CTR block list. -/
theorem Inv.blocks_end {s₀ s : State} (hI : Inv s₀ (nBlk s₀) (nBlk s₀) s) :
    blocksAt s.mem ((datP s₀).setWidth 64) (nBlk s₀) =
      Spec.Gcm.ctr32 (ciph s₀) (cb s₀)
        (blocksAt s₀.mem ((datP s₀).setWidth 64) (nBlk s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nBlk s₀ := by simpa [blocksAt] using h₁
    have hb := hI.blocks k hk
    simp only [hk, ite_true] at hb
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map,
      List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
    exact hb

/-- Complete functional correctness and cdecl ABI preservation. -/
theorem correct {s₀ : State} (hp : CPre s₀) :
    WP isa Impl.Aes.X86.AesNi.ctr32 s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Aes.ctr32X86.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok s₀ hp) fun s₁ hs => ?_)
  refine loops_ok hp (Inv.of_start hp hs) hs.cf _ fun s₂ hI => ?_
  refine WP.mono (restore_ok hp (nBlk s₀) hI.saved hI.edx hI.ebp hI.esp
    hI.rd hI.wr hI.frame hI.ebx) fun s' ⟨habi, hctr, hdata, _, _⟩ => ?_
  refine ⟨habi, ?_, hctr⟩
  rw [hdata]
  exact hI.blocks_end

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86.post s s' :=
  (correct (CPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_verified :
    Verified X86.target Impl.Aes.X86.AesNi.ctr32 (Spec.Gcm.ctr32Contract X86.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    have a0 : arg ctrSat 0 = 0x1000 := by decide
    have a1 : arg ctrSat 1 = 10 := by decide
    have a2 : arg ctrSat 2 = 0x2000 := by decide
    have a3 : arg ctrSat 3 = 0x3000 := by decide
    have a4 : arg ctrSat 4 = 0 := by decide
    have a5 : arg ctrSat 5 = 0x4000 := by decide
    have e : argAddr ctrSat 0 = 0x8004 := by decide
    have esp : ctrSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.Aes.ctr32X86] [a0, a1, a2, a3, a4, a5, e, esp] using ctrSat)

end VG.Proof.Aes.X86.AesNi
