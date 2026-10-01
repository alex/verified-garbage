import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Nonce

/-! Bind the nonce point, cached public key and message into the signing challenge. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def challenge (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Spec.Ed25519.scalarBase (nonce L m) ++
    Spec.Ed25519.bytesAt m L.pk 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure ChallengeReady (L : Lay) (m : Mem) (t : State) : Prop extends NonceReady L m t where
  challenge : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32 = challenge L m

def challengeCode (v : Compress) : Prog isa := .seq (hashChallenge v.callee v.suffix) (reduce 96)

theorem challenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hs : NonceReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (challengeCode v) t fun t' => Ctx L g mx m₀ t' ∧ ChallengeReady L m₀ t' := by
  have hp : Spec.Ed25519.bytesAt t.mem L.pk 32 = Spec.Ed25519.bytesAt m₀ L.pk 32 :=
    hc.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (hashChallenge_ok v hL hc hlen) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.point, hp, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  have hnu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m₀ :=
    (hash_stk_bytes hL hf (d := 80) (n := 32) (by decide) (by decide)).trans hs.nonce
  have hpu : Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.scalarBase (nonce L m₀) :=
    ((stable_out hL).bytes hf (by decide : 32 ≤ 2 ^ 64)).trans hs.point
  refine WP.mono (reduce_step hL hu 96 (by decide) hd) fun w ⟨hw, hk, hfw⟩ =>
    ⟨hw, ⟨?_, ?_, ?_⟩, hk⟩
  · exact (reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  · exact (reduce_stk_bytes hL hfw (d := 80) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hnu
  · exact (reduce_out_bytes hL hfw (by decide)).trans hpu

end VG.Proof.Ed25519.X86_64.SignCached
