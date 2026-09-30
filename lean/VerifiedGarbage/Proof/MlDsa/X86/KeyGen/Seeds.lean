import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inv

/-!
# ML-DSA key generation on x86 (32-bit): the seeds

Untrusted: everything here is checked by Lean. `esi ← scratch`, the AND of
the samplers' results set to 1, `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`, `ρ` to the
seed of `RejNTTPoly` and `ρ′ ‖ · ‖ 0` to that of `RejBoundedPoly`
(`seeds_piece`, which ends in `KB` with the AND 1).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- SHAKE256 as the sponge functions compute it. -/
theorem sponge_H (m : List Byte) (d : Nat) :
    Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 ((BitVec.ofNat 32 0x1f).setWidth 8) m)) 0 d =
      Spec.MlDsa.H m d := by
  rw [show (BitVec.ofNat 32 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix from Proof.MlKem.shakeSuffix32]
  exact (Proof.MlKem.shake256_eq m d).symm

theorem seeds_eq (p : Params) (ξ : List Byte) :
    keyGenSeeds p ξ = ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).take 32,
      ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).drop 32).take 64,
      ((Spec.MlDsa.H (ξ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128).drop 96).take 32) := rfl

section
variable {p : Params}

/-- After `oACC ← 1`. -/
abbrev A1 (p : Params) (s₀ s : State) : Prop := Ctx (YK p) s₀ s ∧ accV s₀ s = 1

theorem acc_keep {s₀ s s' : State} (hp : TPre (YK p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : (YK p).apart (sb oACC 4) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    accV s₀ s' = accV s₀ s := keepW hp hN hs fr

theorem seeds_piece (hF : PFacts p) :
    KP p (fun s₀ s => s = P0 s₀) (fun s₀ s => KB p s₀ s ∧ accV s₀ s = 1)
      (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * kS)))]) (seeds p)) := by
  have hk := hF.k; have hl := hF.l
  refine Piece.seq (ldsc_piece (Y := YK p) (ht := .block []) (by kernel_rfl)) ?_
  unfold seeds
  refine Piece.seq (B := A1 p) (st32_piece (Y := YK p) oACC 1 (by layp hF) (by taint_decide) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [accV, m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oKL 1)) 1 = [BitVec.ofNat 8 p.k])
    (st8_piece (Y := YK p) oKL p.k (by layp hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' m' => ⟨⟨h', by rw [acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.2⟩,
        by rw [m', YK_sc]; exact st8_bytes _ _ _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oKL 2)) 2 =
      integerToBytes p.k 1 ++ integerToBytes p.ℓ 1)
    (st8_piece (Y := YK p) (oKL + 1) p.ℓ (by layp hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1)
      fun s₀ s s' hp h h' m' => ⟨⟨h', by rw [acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.1.2⟩,
        ?_⟩) ?_
  · rw [bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), Proof.MlDsa.KeyGen.integerToBytes_one,
      Proof.MlDsa.KeyGen.integerToBytes_one, keepBytes hp (N := 0) (stkN (by omega)) (by layp hF) (m' ▸ frW8), h.2, m', YK_sc,
      st8_bytes]
  refine Piece.seq (B := fun s₀ s => A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = hxOf p s₀)
    (hash2_piece (Y := YK p) 0 200 136 0x1f ⟨0, 0, 32⟩ (sb oKL 2) (sb oHX 128) Proof.MlKem.rate136 (by layp hF)
      (by rw [YK_stk]; omega) (by decide) (by decide) (by decide) (by taint_decide)
      (h₁ := .block []) (by kernel_rfl) (h₂ := .block []) (by kernel_rfl) (h₃ := .block []) (by kernel_rfl)
      (h₄ := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr out => ⟨⟨h',
        by rw [acc_keep hp (N := 40) (by omega) (by layp hF) fr]; exact h.1.2⟩, ?_⟩) ?_
  · rw [out, h.2, Ctx.roBytes hp h.1.1 (b := ⟨0, 0, 32⟩) (by layp hF) rfl, sponge_H, hxOf, List.append_assoc]
  refine Piece.seq (B := fun s₀ s => A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = hxOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = rhoOf p s₀)
    (copyW_piece (Y := YK p) kS oHX kS oSA 8 (by decide) (by decide) (by layp hF) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr cp => ⟨⟨h',
        by rw [acc_keep hp (N := 0) (by omega) (by layp hF) (fr1 fr)]; exact h.1.2⟩,
        by rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oHX 128) (by layp hF) (fr1 fr)]; exact h.2, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ (sb oSA 32)) 32 = _
    rw [cp]
    show bytesAt s.mem (Buf.addr s₀ (sb oHX 32)) 32 = (keyGenSeeds p (xiOf s₀)).1
    rw [seeds_eq]
    show _ = (hxOf p s₀).take 32
    rw [← h.2, Proof.MlKem.bytesAt_take _ _ (by decide)]
  refine Piece.seq (B := fun s₀ s => A1 p s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = hxOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = rhoOf p s₀ ∧
      bytesAt s.mem (Buf.addr s₀ (sb oSB 64)) 64 = rho'Of p s₀)
    (copyW_piece (Y := YK p) kS (oHX + 32) kS oSB 16 (by decide) (by decide) (by layp hF) (h₁ := .block [])
      (by kernel_rfl) (by taint_decide) (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr cp => ⟨⟨h',
        by rw [acc_keep hp (N := 0) (by omega) (by layp hF) (fr1 fr)]; exact h.1.2⟩,
        by rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oHX 128) (by layp hF) (fr1 fr)]; exact h.2.1,
        by rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oSA 32) (by layp hF) (fr1 fr)]; exact h.2.2, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ (sb oSB 64)) 64 = _
    rw [cp]
    show bytesAt s.mem (Buf.addr s₀ (sb (oHX + 32) 64)) 64 = (keyGenSeeds p (xiOf s₀)).2.1
    rw [seeds_eq]
    show _ = ((hxOf p s₀).drop 32).take 64
    rw [← h.2.1, bytes_sub hp _ (k := 32) (c := 64) (L := 128) (by decide) (by layp hF) (by layp hF)]
  refine st8_piece (Y := YK p) (oSB + 65) 0 (by layp hF) (by taint_decide) (fun _ _ _ h => h.1.1)
    fun s₀ s s' hp h h' m' => ⟨⟨h', ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oHX 128) (by layp hF) (m' ▸ frW8)]; exact h.2.1
  · rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oSA 32) (by layp hF) (m' ▸ frW8)]; exact h.2.2.1
  · rw [keepBytes hp (N := 0) (stkN (by omega)) (b := sb oSB 64) (by layp hF) (m' ▸ frW8)]; exact h.2.2.2
  · rw [m', YK_sc, st8_bytes]; rfl
  · rw [acc_keep hp (N := 0) (by omega) (by layp hF) (m' ▸ frW8)]; exact h.1.2

end

end VG.Proof.MlDsa.X86.KeyGen
