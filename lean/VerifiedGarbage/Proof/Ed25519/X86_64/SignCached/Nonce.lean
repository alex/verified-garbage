import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Secret
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Calls

/-! Hash and reduce the deterministic nonce, then encode its base-point multiple. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem L.out 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

def nonceCode (fld : VG.Impl.Ed25519.X86_64.Arith) (fs : String) (v : Compress) : Prog isa :=
  .seq (hashNonce v.callee v.suffix) (.seq (reduce 64)
    (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)))

theorem nonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hs : SecretReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (nonceCode fld fs v) t fun t' => Ctx L g mx m₀ t' ∧ NonceReady L m₀ t' := by
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (hashNonce_ok v hL hc (by omega)) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.prefixBytes, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hL hu 64 (by decide) hd) fun w ⟨hw, hn, hfw⟩ => ?_)
  change Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m₀ at hn
  have hsw : Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  refine WP.mono (base_step hL hw hn) fun z ⟨hz, hp, hfz⟩ => ⟨hz, ?_, ?_, hp⟩
  · exact (base_stk_bytes hL hfz (d := 16) (n := 32) (by decide) (by decide)).trans hsw
  · exact (base_stk_bytes hL hfz (d := 80) (n := 32) (by decide) (by decide)).trans hn

end VG.Proof.Ed25519.X86_64.SignCached
