import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTBody
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Correct
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 5 p)
    (hqb : Whole.Saved (Whole.entered t) 5 q) :
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).pk) 32 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).pk) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).msg) (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (State.addr (lay s).msg) (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).sig) 64 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).sig) 64 := by
  have fp := Whole.saved_frame (entry_below hs) hpa
  have fq := Whole.saved_frame (entry_below ht) hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨State.addr (t.gpr .r0),32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [hs.1]; simp)
    (by have := (s.gpr .r2).isLt; change (s.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have fmsg := entry_input ht fq (r := ⟨State.addr (t.gpr .r1),(t.gpr .r2).toNat⟩) (by rw [ht.1]; simp)
    (by have := (t.gpr .r2).isLt; change (t.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have esig := entry_input hs fp (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨State.addr (t.gpr .r3),64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r0)) 32=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r3)) 64=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r3)) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub code := by
  refine Whole.wrap_ct (by decide : 5 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) (fun _ hs => entry_top hs) (fun _ hs => entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct (lay_ok hs) (entry_args hs hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
