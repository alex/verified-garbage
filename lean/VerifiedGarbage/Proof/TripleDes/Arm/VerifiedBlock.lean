import VerifiedGarbage.Proof.TripleDes.Arm.Pre
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧ (blockContract d).post s s') := by
  have hp := headPre_of_contract d s hs
  have hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    intro t ht
    have fit := hs.2.2.2.2.2.1
    rw [addr_add (by omega_using [fit, ht]), hs.2.1]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r0) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, hpost.sp⟩, hpost.result⟩
  intro r hr
  have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ roundStepKept := by decide
  rcases hkeep r hr with h | h
  · exact hpost.saved r h
  · exact hpost.regs r h

theorem encrypt_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : PublicRegs [.r0, .r1, .r2] s t ↔
    s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    blockContract, publicRegs_three, blockResult] [satState] using satState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    blockContract, publicRegs_three, blockResult] [satState] using satState

end VG.Proof.TripleDes.Arm
