import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inv
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps

/-!
# ML-DSA key generation on 32-bit ARM: the seeds

Untrusted: everything here is checked by Lean. `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)`
to `HX`, `ρ` to the seed of `RejNTTPoly` and `ρ′ ‖ 0` to that of
`RejBoundedPoly` (`seeds_piece`, `K1`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  kc : KC p STK σ s
  hx : bytesAt s.mem ((lay p STK σ).A 0 oHX) 128 = hxOf p σ
  sa : bytesAt s.mem ((lay p STK σ).A 0 oSA) 32 = rhoOf p σ
  sb : bytesAt s.mem ((lay p STK σ).A 0 oSB) 64 = rho'Of p σ
  z : bytesAt s.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0]

/-- A part that writes the regions `W` keeps `K1`. -/
def k1Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  kcChk p STK W && sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oHX, 128) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSA, 32) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB, 64) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB + 65, 1) W

theorem K1.keep {p : Params} {STK : Nat} {σ s s' : State} (h : K1 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : k1Chk p STK W = true) : K1 p STK σ s' := by
  simp only [k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.kc.site.ok
  exact ⟨h.kc.keep hk h0, by rw [bytes_keepW hL hk.frame h1 (by decide) (by decide)]; exact h.hx,
    by rw [bytes_keepW hL hk.frame h2 (by decide) (by decide)]; exact h.sa,
    by rw [bytes_keepW hL hk.frame h3 (by decide) (by decide)]; exact h.sb,
    by rw [bytes_keepW hL hk.frame h4 (by decide) (by decide)]; exact h.z⟩

theorem shake31 : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem hx_eq (p : Params) (σ : State) :
    hxOf p σ = Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 31)
      (xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ])))) 0 128 := by
  rw [hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, shake31,
    List.append_assoc]
  exact Proof.MlKem.shake256_eq _ _

theorem rho_eq (p : Params) (σ : State) : rhoOf p σ = (hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : rho'Of p σ = ((hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : kOf p σ = ((hxOf p σ).drop 96).take 32 := rfl

theorem sc_ok (o : Nat) : argOk (.ptr (sc o)) = true := rfl

theorem seeds_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {s : State}
    (h : KC p STK σ s) (h11 : s.gpr .r11 = 1) : WP isa (seeds p) s fun s' => K1 p STK σ s' ∧ s'.gpr .r11 = 1 := by
  have hk := hF.k; have hl := hF.l
  have hs := h.site
  unfold seeds
  -- `k` and `ℓ`
  have blk : WP isa (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ)) s fun s₂ =>
      KC p STK σ s₂ ∧ s₂.gpr .r11 = 1 ∧
        bytesAt s₂.mem ((lay p STK σ).A 0 oKL) 2 = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    refine WP.block_append (WP.mono (setB_ok hs (q := sc oKL) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, b₂⟩ => ⟨(h.keep k₁ (by lsep hF [kcChk])).keep k₂ (by lsep hF [kcChk]), ?_, ?_⟩)
    · rw [k₂.cs .r11 (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), h11]
    · have b₁' := bytes_keepW hs.ok k₂.frame (i := 0) (o := oKL) (l := 1) (by lsep hF) (by decide) (by decide)
      rw [show (2 : Nat) = 1 + 1 from rfl, Proof.MlKem.bytesAt_add, b₁'.trans b₁, add_ofNat_add]
      exact congrArg _ b₂
  refine WP.seq (WP.mono blk fun s₂ ⟨h₂, r₂, b₂⟩ => ?_)
  -- `H(ξ ‖ k ‖ ℓ, 128)`
  have hs₂ := h₂.site
  have hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
      i ∈ kWb ∨ j ∈ kWb := fun i hi j hj hij _ _ _ _ => by
    simp only [kWb, List.mem_cons, List.not_mem_nil, or_false]; omega
  refine WP.seq (WP.mono (hashS hs₂ hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
      (ins := [⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩]) (q := ⟨.r7, oHX, 128⟩) (by simp) (fun pc hpc => ?_)
      (pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size]) (.inl rfl)
        fun _ => by decide)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have h₃ := h₂.keep k₃ (by lsep hF [kcChk])
  have hs₃ := h₃.site
  have hx₃ : bytesAt s₃.mem ((lay p STK σ).A 0 oHX) 128 = hxOf p σ := by
    have o₃' : bytesAt s₃.mem ((lay p STK σ).A 0 oHX) 128 = _ := o₃
    rw [o₃', hx_eq]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s₂.mem (State.addr ((lay p STK σ).ptr (ix Reg.r4)) + 0#64) 32 = xiOf σ := h₂.xi
    have e2 : bytesAt s₂.mem (State.addr ((lay p STK σ).ptr (ix Reg.r7)) + BitVec.ofNat 64 oKL) 2 =
      [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := b₂
    rw [e1, e2]; rfl
  -- `ρ` and `ρ′ ‖ 0` to the seeds
  refine WP.seq (WP.mono (copyS hs₃ (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
    fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep k₄ (by lsep hF [kcChk])
  have hx₄ := (bytes_keepW hs₃.ok k₄.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)).trans hx₃
  refine WP.seq (WP.mono (copyS h₄.site (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by lsep hF)) fun s₅ ⟨k₅, b₅⟩ => ?_)
  have h₅ := h₄.keep k₅ (by lsep hF [kcChk])
  refine WP.mono (setB_ok h₅.site (q := sc (oSB + 65)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) 0)
    fun s₆ ⟨k₆, b₆⟩ => ⟨⟨h₅.keep k₆ (by lsep hF [kcChk]), ?_, ?_, ?_, b₆⟩, ?_⟩
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide),
      bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)]
    exact hx₄
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide),
      bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₄.mem (lpa (lay p STK σ) (.r7, oSA)) 32 = _
    rw [b₄, rho_eq, ← hx₃]
    exact (Proof.MlKem.bytesAt_take _ _ (by decide)).symm
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₅.mem (lpa (lay p STK σ) (.r7, oSB)) 64 = _
    rw [b₅, rho'_eq, ← hx₄, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide), add_ofNat_add]
    rfl
  · rw [k₆.cs .r11 (by decide) (by decide), k₅.cs .r11 (by decide) (by decide), k₄.cs .r11 (by decide) (by decide),
      k₃.cs .r11 (by decide) (by decide), r₂]

end VG.Proof.MlDsa.Arm.KeyGen
