import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Entry

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_ok (backend : Whole.Backend) {s : State} (h : verifyMessageLocal.pre s) :
    WP isa (code backend.code backend.suffix) s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth backend) (entry_below h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) 64)))
    (fun p hp => WP.mono (body_ok backend (entry_ctx h hp) (lay_ok h) (entry_args hp))
      fun u ⟨hu,ho⟩ => ⟨by
        simpa only [Whole.bodyRd,h.1,Ctx,Lay.inputs,Lay.outputs,Lay.PK,Lay.MSG,Lay.SIG,
          Lay.SCR,Lay.ARGS,lay,h.2.1,List.cons_append,List.nil_append] using hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨s.gpr .x0,32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .x2).toNat≤2^64; exact Nat.le_of_lt (s.gpr .x2).isLt)
  have sig := entry_input h hf (r := ⟨s.gpr .x3,64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .x0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.AArch64.VerifyMessage
