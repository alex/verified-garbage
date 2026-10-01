import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Preserve

/-! Expand the seed and save both the pruned scalar and the nonce prefix. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem saveSecret_ok {t : State} (hc : Ctx L g mx m₀ t) {expanded : List Byte}
    (he : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = expanded) :
    WP isa (.block saveSecret) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 = expanded.drop 32 := by
  rw [saveSecret, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prune_ok hc he) fun u ⟨hu, hf, hs⟩ => ?_
  have hd : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 144) 64 = expanded :=
    (single_stk_bytes hf (by decide) (by decide) (by decide)).trans he
  refine WP.mono (prefix_ok hu) fun w ⟨hw, hfw, hp⟩ => ⟨hw, ?_, ?_⟩
  · rw [single_stk_bytes hfw (by decide : 16 + 32 ≤ 48 ∨ 48 + 32 ≤ 16) (by decide) (by decide)]
    rw [Proof.Ed25519.bytesAt_encodeLE u.mem, hs]
  · rw [hp, hd]

def expanded (L : Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m L.seed 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 = (expanded L m).drop 32

theorem secret_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.seq (hashSeed v.callee v.suffix) (.block saveSecret)) t fun t' =>
      Ctx L g mx m₀ t' ∧ SecretReady L m₀ t' := by
  have he : Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 :=
    hc.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  refine WP.seq (WP.mono (hashSeed_ok v hL hc) fun u ⟨hu, hd, _⟩ => ?_)
  rw [he] at hd
  exact WP.mono (saveSecret_ok hu hd) fun w ⟨hw, hs, hp⟩ => ⟨hw, hs, hp⟩

end VG.Proof.Ed25519.X86_64.SignCached
