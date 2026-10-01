import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CTHashes
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CTCalls
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Correct

/-! Complete signing is constant-time with respect to seed, key and message bytes. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem body_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (body v.callee v.suffix) (Two fun _ _ _ => True) := by
  have s : RelCT isa (Two fun _ _ _ => True) (.block saveSecret) (Two fun _ _ _ => True) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (saveSecret_ok hc rfl) fun _ ⟨hc', _, _⟩ => ⟨hc', trivial⟩
  have w : RelCT isa (Two fun _ _ _ => True) (.block wipe) (Two fun _ _ _ => True) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (wipe_ok hc) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact (hashSeed_ct v).seq (s.seq ((hashNonce_ct v).seq ((reduce_ct 64 (by decide) (by taint_decide)).seq
    (base_ct.seq ((hashChallenge_ct v).seq ((reduce_ct 96 (by decide) (by taint_decide)).seq (mul_ct.seq w)))))))

theorem sign_ct (v : Compress) : ConstantTime isa signLocal.pre signLocal.pub (code v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, h9⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx, hcx, h8, h9]
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁,
    push_ctx h₁, e ▸ push_ctx h₂, trivial, trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
