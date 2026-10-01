import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.HashSteps

/-! The signer's three hashes, using any verified SHA-512 backend. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem hashSeed_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (hashSeed v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem L.seed 32) ∧ HashFrame L t.mem t'.mem := by
  have hi := stable_input hL (r := L.SEED) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (update_step v hL hc₁ (prev := []) (n := 32) hi.toInput
    (inputArgs_ok hc₁ fSeed 0 (by decide) (by decide) L.seed hc₁.pSeed) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem L.seed 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem L.seed 32 = Spec.Ed25519.bytesAt t.mem L.seed 32 at he
  rw [he] at hr₂
  refine WP.mono (finalize_step v hL hc₂ 32 (by decide) false ?_ ?_ hr₂)
    fun t₃ ⟨hc₃, hd₃, hf₃⟩ => ⟨hc₃, hd₃, hf₁.trans (hf₂.trans hf₃)⟩
  · rw [PublicKey.bytesAt_length]; decide
  · rw [PublicKey.bytesAt_length]; rfl

theorem hashNonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 32 + L.len.toNat < 2 ^ 64) :
    WP isa (hashNonce v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 ++
          Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧ HashFrame L t.mem t'.mem := by
  have hi := stable_prefix hL
  have hm := stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (update_step v hL hc₁ (prev := []) (n := 32) hi.toInput (prefixArgs_ok hc₁) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32 = Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 at he
  rw [he] at hr₂
  have ha := messageArgs_ok hc₂ 32 (by decide)
  rw [← PublicKey.bytesAt_length t.mem (L.B + BitVec.ofNat 64 48) 32] at ha
  refine WP.seq (WP.mono (update_step v hL hc₂ (n := L.len) hm.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heM := hm.bytes (hf₁.trans hf₂) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₃
  refine WP.mono (finalize_step v hL hc₃ 32 (by decide) true ?_ ?_ hr₃)
    fun t₄ ⟨hc₄, hd₄, hf₄⟩ => ⟨hc₄, hd₄, hf₁.trans (hf₂.trans (hf₃.trans hf₄))⟩
  · simpa only [List.length_append, PublicKey.bytesAt_length] using hlen
  · simp only [List.length_append, PublicKey.bytesAt_length, ite_true,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]


theorem hashChallenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (hashChallenge v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
          Spec.Ed25519.bytesAt t.mem L.pk 32 ++ Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧
      HashFrame L t.mem t'.mem := by
  have hi := stable_out hL
  have hk := stable_input hL (r := L.PK) (by simp [Lay.inputs])
  have hm := stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (update_step v hL hc₁ (prev := []) (n := 32) hi.toInput
    (inputArgs_ok hc₁ fOut 0 (by decide) (by decide) L.out hc₁.pOut) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem L.out 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 at he
  rw [he] at hr₂
  have ha := inputArgs_ok hc₂ fPublicKey 32 (by decide) (by decide) L.pk hc₂.pPk
  rw [← PublicKey.bytesAt_length t.mem L.out 32] at ha
  refine WP.seq (WP.mono (update_step v hL hc₂ (n := 32) hk.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heK := hk.bytes (hf₁.trans hf₂) (by decide : 32 ≤ 2 ^ 64)
  change Spec.Ed25519.bytesAt t₂.mem L.pk 32 = Spec.Ed25519.bytesAt t.mem L.pk 32 at heK
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₃.mem L.scr
    (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t₂.mem L.pk 32) at hr₃
  rw [heK] at hr₃
  have haM := messageArgs_ok hc₃ 64 (by decide)
  have hn : (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t.mem L.pk 32).length = 64 := by
    simp only [List.length_append, PublicKey.bytesAt_length]
  have haM' : WP isa (.block (messageArgs 64)) t₃ fun u => Ctx L g mx m₀ u ∧ u.mem = t₃.mem ∧
      UpdArgs L (BitVec.ofNat 64 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
        Spec.Ed25519.bytesAt t.mem L.pk 32).length) L.msg L.len u := by
    rw [hn]; exact haM
  refine WP.seq (WP.mono (update_step v hL hc₃ (n := L.len) hm.toInput haM' hr₃)
    fun t₄ ⟨hc₄, hr₄, hf₄⟩ => ?_)
  have heM := hm.bytes (hf₁.trans (hf₂.trans hf₃)) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₄
  refine WP.mono (finalize_step v hL hc₄ 64 (by decide) true ?_ ?_ hr₄)
    fun t₅ ⟨hc₅, hd₅, hf₅⟩ => ⟨hc₅, hd₅, hf₁.trans (hf₂.trans (hf₃.trans (hf₄.trans hf₅)))⟩
  · simpa only [List.length_append, PublicKey.bytesAt_length] using hlen
  · simp only [List.length_append, PublicKey.bytesAt_length, ite_true,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
    rfl

end VG.Proof.Ed25519.X86_64.SignCached
