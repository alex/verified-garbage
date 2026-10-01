import VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.Arm.MulKeep

/-! Untrusted: decoding writes the saved sign and field workspace only. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure DecodeKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: clob) s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 60, 4⟩, FA b] s.mem t.mem

theorem DecodeKeep.ctx {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem DecodeKeep.trans {b : BitVec 32} {s t u : State} (h : DecodeKeep b s t) (k : DecodeKeep b t u) :
    DecodeKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem DecodeKeep.of_ikeep {b : BitVec 32} {s t : State} (h : IKeep b s t) : DecodeKeep b s t :=
  ⟨h.rest, h.frame.mono (fun _ hr => List.mem_cons_of_mem _ hr)⟩
theorem DecodeKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : DecodeKeep b s t :=
  DecodeKeep.of_ikeep (IKeep.of_keep h)

end VG.Proof.Ed25519.Arm
