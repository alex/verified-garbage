import VerifiedGarbage.Impl.MlKem.Arm.Top

/-!
# ML-KEM on 32-bit ARM: what the proofs need of a parameter set

The proofs of the top-level functions (`KeyGen.lean`, `Encaps.lean`,
`Decaps.lean`, …) hold for any parameter set `K : KemLay` that passes
`KemLay.wf`: a computation on the literals of `K`, which each parameter set
checks by `decide` (`kl768_wf` here, ML-KEM-1024's in `Proof/MlKem1024/Arm/`).
The proofs use it as facts (`KemLay.WF`): `1 ≤ k ≤ 4`, a `scratch` of at
least 32 KiB, `η₁ = η₂ = 2`, the
shifts of `atU`, that the buffers of decapsulation fit in `scratch`, and that
the immediates that depend on the parameters are encodable. Facts on the
offsets in `scratch` that follow from `k ≤ 4` alone, the proofs decide by
`omega` (`kdecide`, `Prf.lean`).
-/

namespace VG.Impl.MlKem.Arm

open VG VG.Arm

/-- What the proofs need of the parameters, as facts. -/
structure KemLay.WF (K : KemLay) : Prop where
  k1 : 1 ≤ K.k
  k4 : K.k ≤ 4
  scr : 32768 ≤ K.scratch
  η₁ : K.p.η₁ = 2
  η₂ : K.p.η₂ = 2
  du1 : 1 ≤ K.du
  du : K.du ≤ 11
  dv : K.dv ≤ 11
  sh : K.uShifts.all (fun t => 1 ≤ t && t ≤ 31) = true
  shSum : (K.uShifts.map (2 ^ ·)).sum = K.uLen
  ct : K.oCt + K.ctLen ≤ oCin
  cin : oCin + K.ctLen ≤ 32768
  encDu : encodable (BitVec.ofNat 32 K.du) = true
  encDv : encodable (BitVec.ofNat 32 K.dv) = true
  encU : encodable (BitVec.ofNat 32 K.uLen) = true
  encV : encodable (BitVec.ofNat 32 K.vLen) = true
  encVo : encodable (BitVec.ofNat 32 (K.uLen * K.k)) = true
  encCt : encodable (BitVec.ofNat 32 K.ctLen) = true
  encEk : encodable (BitVec.ofNat 32 K.ekLen) = true
  encT : encodable (BitVec.ofNat 32 (384 * K.k)) = true
  encH : encodable (BitVec.ofNat 32 (768 * K.k + 32)) = true
  encZ : encodable (BitVec.ofNat 32 (768 * K.k + 64)) = true

/-- `KemLay.WF` as a computation. -/
def KemLay.wf (K : KemLay) : Bool :=
  decide (1 ≤ K.k) && (decide (K.k ≤ 4) && (decide (32768 ≤ K.scratch) && (decide (K.p.η₁ = 2) && (decide (K.p.η₂ = 2) &&
  (decide (1 ≤ K.du) && (decide (K.du ≤ 11) && (decide (K.dv ≤ 11) && (K.uShifts.all (fun t => 1 ≤ t && t ≤ 31) &&
  (decide ((K.uShifts.map (2 ^ ·)).sum = K.uLen) && (decide (K.oCt + K.ctLen ≤ oCin) &&
  (decide (oCin + K.ctLen ≤ 32768) && (encodable (BitVec.ofNat 32 K.du) && (encodable (BitVec.ofNat 32 K.dv) &&
  (encodable (BitVec.ofNat 32 K.uLen) && (encodable (BitVec.ofNat 32 K.vLen) &&
  (encodable (BitVec.ofNat 32 (K.uLen * K.k)) && (encodable (BitVec.ofNat 32 K.ctLen) &&
  (encodable (BitVec.ofNat 32 K.ekLen) && (encodable (BitVec.ofNat 32 (384 * K.k)) &&
  (encodable (BitVec.ofNat 32 (768 * K.k + 32)) && encodable (BitVec.ofNat 32 (768 * K.k + 64))))))))))))))))))))))

theorem KemLay.WF.of {K : KemLay} (h : K.wf = true) : K.WF := by
  simp only [KemLay.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

end VG.Impl.MlKem.Arm

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm

theorem kl768_wf : kl768.WF := .of (by decide)

/-- The polynomials of `scratch` have encodable offsets. -/
theorem enc_poly : ∀ j < 21, encodable (BitVec.ofNat 32 (oPoly j)) = true := by decide

theorem _root_.VG.Impl.MlKem.Arm.KemLay.WF.enc {K : KemLay} (hK : K.WF) {j : Nat} (hj : j ≤ 3 * K.k + 8) :
    encodable (BitVec.ofNat 32 (oPoly j)) = true :=
  enc_poly j (by have := hK.k4; omega)

theorem _root_.VG.Impl.MlKem.Arm.KemLay.WF.ct_pos {K : KemLay} (hK : K.WF) : 0 < K.ctLen := by
  have h1 : 0 < K.uLen := by simp only [KemLay.uLen]; have := hK.du1; omega
  have h2 : K.uLen ≤ K.uLen * K.k := Nat.le_mul_of_pos_right _ hK.k1
  simp only [KemLay.ctLen]; omega

end VG.Proof.MlKem.Arm
