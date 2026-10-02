import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyLen)

/-- The independently checked bodies used by the public-length dispatcher. -/
structure KeyBodies : Prop where
  expand128 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 16 →
    WP isa (.block Impl.Aes.X86.AesNi.expand128) entry (KeyDone s₀ entry 4)
  expand192 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 24 →
    WP isa (.block Impl.Aes.X86.AesNi.expand192) entry (KeyDone s₀ entry 6)
  expand256 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 32 →
    WP isa (.block Impl.Aes.X86.AesNi.expand256) entry (KeyDone s₀ entry 8)

/-- Complete expansion, with public dispatch on the key length. -/
theorem key_dispatch_correct (bodies : KeyBodies) {s₀ : State} (hp : EPre s₀) :
    WP isa Impl.Aes.X86.AesNi.expandKey s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Aes.expandKeyX86.post s₀ s' := by
  refine WP.seq (WP.mono (keyHead_ok s₀ hp) fun entry hs => ?_)
  refine WP.ite (decide (arg s₀ 1 = 24#32)) (by simp [eval, hs.zf]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    have hl : keyLen s₀ = 24 := congrArg BitVec.toNat h
    refine WP.mono (bodies.expand192 s₀ entry hp hs.toKeyReady hl) fun s hd => ?_
    exact ⟨hd.abi hp hs.toKeyReady, hd.post (by decide) hl⟩
  · simp only [decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (keyCmp32_ok hs.toKeyReady) fun mid ⟨hm, hz⟩ => ?_)
    refine WP.ite (decide (arg s₀ 1 = 32#32)) (by simp [eval, hz]) (fun h32 => ?_) (fun h32 => ?_)
    · simp only [decide_eq_true_eq] at h32
      have hl : keyLen s₀ = 32 := congrArg BitVec.toNat h32
      refine WP.mono (bodies.expand256 s₀ mid hp hm hl) fun s hd => ?_
      exact ⟨hd.abi hp hm, hd.post (by decide) hl⟩
    · simp only [decide_eq_false_iff_not] at h32
      have h24 : keyLen s₀ ≠ 24 := fun e => h (BitVec.eq_of_toNat_eq e)
      have hN32 : keyLen s₀ ≠ 32 := fun e => h32 (BitVec.eq_of_toNat_eq e)
      have hl : keyLen s₀ = 16 := by have := hp.len; omega
      refine WP.mono (bodies.expand128 s₀ mid hp hm hl) fun s hd => ?_
      exact ⟨hd.abi hp hm, hd.post (by decide) hl⟩

end VG.Proof.Aes.X86.AesNi
