import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
import VerifiedGarbage.Proof.MlDsa.Verify.Spec

/-!
# ML-DSA verification on 32-bit ARM: the primitives, and the hint

The primitives verification calls, verified with at most `S` bytes of stack
(`VPrimsOk`); and the hint `h` of the signature, unpacked to polynomials `0,
…, k - 1`, with `r11` 1 if it is well formed and 0 if not (`hint_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee HbuOk hbu_okS
  hbu_tr)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params HintIs hintBitUnpack)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure VPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract Arm.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract Arm.abi stk) S
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract Arm.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract Arm.abi stk) S
  sub : Callee P.sub (fun stk => Spec.MlDsa.subContract Arm.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract Arm.abi stk) S
  ball : Callee P.ball (fun stk => Spec.MlDsa.sampleInBallContract Arm.abi stk) S
  useHint : Callee P.useHint (fun stk => Spec.MlDsa.useHintContract Arm.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract Arm.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => Spec.MlDsa.bitUnpackContract Arm.abi stk) S
  unpackT1 : Callee P.unpackT1 (fun stk => Spec.MlDsa.unpackT1Contract Arm.abi stk) S
  hintUnpack : Callee P.hintUnpack (fun stk => Spec.MlDsa.hintBitUnpackContract Arm.abi stk) S
  normLt : Callee P.normLt (fun stk => Spec.MlDsa.normLtContract Arm.abi stk) S

/-- 1 if `b`, 0 if not. -/
def flag (b : Bool) : BitVec 32 := if b then 1 else 0

/-! ## The signature -/

/-- `h`, or `⊥`, of the signature of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (sgOf p σ)

/-- Bytes of the signature, from its bytes in memory. -/
theorem sig_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.sigLen) :
    bytesAt s.mem ((vlay p STK σ).A 4 o) l = ((sgOf p σ).drop o).take l := by
  have e := h.sg
  simp only [Lay.A, add_ofNat_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-- Bytes of the public key, from its bytes in memory. -/
theorem pk_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.pkLen) :
    bytesAt s.mem ((vlay p STK σ).A 2 o) l = ((pkOf p σ).drop o).take l := by
  have e := h.pk
  simp only [Lay.A, add_ofNat_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-! ## The hint -/

/-- After the hint. -/
structure V1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  r11 : s.gpr .r11 = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem hint_m {σ : State} :
    HbuOk (vlay p STK σ) vWb (.r6, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k) := by
  have hk := hF.k; have hom := hF.om
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF,
    by rw [Nat.add_sub_cancel_left]; exact hF.hp, by omega, by rw [Nat.add_sub_cancel_left], by omega⟩

/-- After the call of `HintBitUnpack`: its result in `r0`. -/
structure H1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  r0 : s.gpr .r0 = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

theorem hbu_ok' {σ s : State} (h : VC p STK σ s) :
    WP isa (hintUnpackAt P (.r6, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) s (H1 p STK σ) := by
  have hs := h.site
  unfold hintUnpackAt
  refine hbu_okS hP.hintUnpack hs (by omega) (hint_m hF) fun s' k' hm => ?_
  have h' := h.keep k' (by vsep hF [vcChk])
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.r6, oHint p)) (p.ω + p.k) =
      ((sgOf p σ).drop (oHint p)).take (p.ω + p.k) := sig_slice h (by rw [hF.sig])
  rw [eb, Nat.add_sub_cancel_left] at hm
  refine ⟨h', ?_, fun hh e => ?_⟩
  · show s'.gpr .r0 = flag (hintBitUnpack p.ω p.k (((sgOf p σ).drop (oHint p)).take (p.ω + p.k))).isSome
    split at hm
    · rename_i hh e; rw [e]; exact hm.1
    · rename_i e; rw [e]; exact hm
  · show HintIs s'.mem _ p.k hh
    have e' : hintBitUnpack p.ω p.k ((sgOf p σ).drop (oHint p) |>.take (p.ω + p.k)) = some hh := e
    rw [e'] at hm
    exact hm.2

theorem hbu_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r11 = 1) (H1 p STK)
      (hintUnpackAt P (.r6, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) := by
  refine ⟨fun σ s _ h => hbu_ok' hP hF hS h.1, ?_⟩
  unfold hintUnpackAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.r6, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (lpa (vlay p STK σ) (.r6, oHint p)) (p.ω + p.k))
    (RelCT.exists_ fun σ => hbu_tr hP.hintUnpack (by omega) (hint_m hF)
      fun x y ⟨T, e⟩ => ⟨T.1, T.2.1, T.2.2, e⟩) ?_
  intro σ₁ _ _ _ _ _ pub h₁ h₂
  refine ⟨σ₁, vc_twoL pub h₁.1 h₂.1, ?_⟩
  show bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _ = bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _
  rw [sig_slice h₁.1 (by rw [hF.sig]), pub.2.2.2.2.2.2.2, vlay_pub pub, sig_slice h₂.1 (by rw [hF.sig])]

omit hP hF hS in
theorem mov11_piece : VPiece p STK (H1 p STK) (V1 p STK) (.block [.mov .r11 (.reg .r0)]) := by
  refine ⟨fun σ s _ h => ?_, vrel7 (fun _ _ h => h.vc) (by taint_decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨h.vc.r11 _, by rw [gpr_setReg_self]; exact h.r0, h.hint⟩

theorem hint_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r11 = 1) (V1 p STK) (hint P p) :=
  (hbu_piece hP hF hS).seq mov11_piece

end

end VG.Proof.MlDsa.Arm.Verify
