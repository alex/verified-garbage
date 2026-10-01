import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Entry

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 5 ≤ 6) (entry_below h) (entry_top h) (entry_read h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) 64)))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args h hp))
      fun u ⟨hu,ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat≤2^64; have := (s.gpr .r2).isLt; omega)
  have sig := entry_input h hf (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .r0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.Arm.VerifyMessage
