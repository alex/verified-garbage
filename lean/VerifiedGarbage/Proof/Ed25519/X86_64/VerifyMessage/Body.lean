import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Equation

/-! Correctness of the complete verifier's frame body. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem extend_reduced {t : State} (hc : Ctx L g mx m₀ t) {digest : List Byte}
    (hr : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (extend_ok hc) fun t' ⟨hc', hf, h0, h1, h2, h3⟩ => ⟨hc', ?_⟩
  have hlo : Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 := by
    apply List.map_congr_left
    intro i hi
    exact Frame.bytes (R := ⟨L.B + BitVec.ofNat 64 16, 32⟩) hf (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : 32 ≤ 2 ^ 64)
      (List.mem_range.mp hi)
  have hhi := zero_words t'.mem (L.B + BitVec.ofNat 64 48) h0
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 8) 64 = 0
        rw [PublicKey.add_add]; exact h1)
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 16) 64 = 0
        rw [PublicKey.add_add]; exact h2)
    (by change t'.mem.readW ((L.B + BitVec.ofNat 64 48) + BitVec.ofNat 64 24) 64 = 0
        rw [PublicKey.add_add]; exact h3)
  have hsplit : Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 64 =
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 ++
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 := by
    have h := Proof.X25519.bytesAt_add t'.mem (L.B + BitVec.ofNat 64 16) 32 32
    rw [PublicKey.add_add] at h
    exact h
  rw [hsplit, hlo, hr, hhi, reduced_challenge]

theorem challengeInput_eq : challengeInput L m₀ =
    (Spec.Ed25519.bytesAt m₀ L.sig 64).take 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32 ++
      Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat := by
  have h : (Spec.Ed25519.bytesAt m₀ L.sig 64).take 32 = Spec.Ed25519.bytesAt m₀ L.sig 32 :=
    PublicKey.take_bytesAt m₀ L.sig
  rw [h]
  rfl

theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (body v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      t'.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verify
        (Spec.Ed25519.bytesAt m₀ L.pk 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat)
        (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono (hash_ok v hL hc hlen) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (reduceArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ =>
    WP.mono (reduce_call hL hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, hr₃⟩ => ?_))
  refine WP.seq (WP.mono (extend_reduced hc₃ hr₃) fun t₄ ⟨hc₄, he₄⟩ => ?_)
  refine WP.seq (WP.mono (equationArgs_ok hc₄) fun t₅ ⟨hc₅, hm₅, ha₅⟩ => ?_)
  have he₅ := hm₅ ▸ he₄
  rw [challengeInput_eq] at he₅
  exact eq_call hL hc₅ ha₅ he₅

end VG.Proof.Ed25519.X86_64.VerifyMessage
