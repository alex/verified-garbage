import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTHashPipeline
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTScalars
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTEquation
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Correct
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem body_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32=Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ L.msg L.len.toNat=Spec.Ed25519.bytesAt m₂ L.msg L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64=Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct backend hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct _).seq (equation_step_ct hL ha hb hpk hsig)))

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 6 p)
    (hqb : Whole.Saved (Whole.entered t) 6 q) :
    Spec.Ed25519.bytesAt p.mem (lay s).pk 32 = Spec.Ed25519.bytesAt q.mem (lay s).pk 32 ∧
    Spec.Ed25519.bytesAt p.mem (lay s).msg (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (lay s).msg (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (lay s).sig 64 = Spec.Ed25519.bytesAt q.mem (lay s).sig 64 := by
  have fp := Whole.saved_frame hpa
  have fq := Whole.saved_frame hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨s.gpr .x0,32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨t.gpr .x0,32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [hs.1]; simp)
    (Nat.le_of_lt (s.gpr .x2).isLt)
  have fmsg := entry_input ht fq (r := ⟨t.gpr .x1,(t.gpr .x2).toNat⟩) (by rw [ht.1]; simp)
    (Nat.le_of_lt (t.gpr .x2).isLt)
  have esig := entry_input hs fp (r := ⟨s.gpr .x3,64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨t.gpr .x3,64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (s.gpr .x0) 32=Spec.Ed25519.bytesAt q.mem (s.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x1) (s.gpr .x2).toNat=Spec.Ed25519.bytesAt q.mem (s.gpr .x1) (s.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x3) 64=Spec.Ed25519.bytesAt q.mem (s.gpr .x3) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct (backend : Whole.Backend) :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub (code backend.code backend.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok backend (entry_ctx hs hp) (lay_ok hs) (entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct backend (lay_ok hs) (entry_args hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
