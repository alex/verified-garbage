import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local

/-!
# ML-DSA verification on x86 (32-bit): the hint and `z`

The pieces of the signature and of the public key are the bytes of their
arguments (`sig_slice`, `pk_slice`), which no piece writes. `HintBitUnpack`
gives the result: 1 with the hint stored (`HOk`), or 0 if it is malformed
(`hint_piece`); then each `z[i]` is unpacked and the result ANDed with
`‖z[i]‖∞ < γ₁ - β` (`zOne_piece`, `ZI`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly PolyIs Reduced polyAt toRq normRq HintIs)
open VG.Proof.MlDsa.Verify (vZ vHint)
open VG.Spec.Sha3 (bytesAt)

theorem lenZ_eq (p : Params) : lenZ p = Proof.MlDsa.Verify.lenZ p := rfl
theorem accB_YV (p : Params) : accB (YV p) = sb oACC 4 := rfl

/-! ## The inputs -/

section
variable {p : Params} (hF : VFacts p) {s₀ s : State} (hp : TPre (YV p) s₀) (h : Ctx (YV p) s₀ s)
include hF hp h

theorem sig_slice {o l : Nat} (hok : (YV p).ok ⟨2, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, o, l⟩) l = ((vSig p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 2) (o := 0) (k := o) (c := l) (L := p.sigLen) hl (by lv hF)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

theorem pk_slice {o l : Nat} (hok : (YV p).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((vPk p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 0) (o := 0) (k := o) (c := l) (L := p.pkLen) hl (by lv hF)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

end

/-! ## The hint -/

section
variable (p : Params) (s₀ : State)

/-- The hint of the signature, or `⊥`. -/
abbrev hOf : Option (List (Vector Bool Spec.MlDsa.n)) := vHint p (vSig p s₀)

/-- The hint, well formed and stored. -/
def HOk (s : State) : Prop := ∃ h, hOf p s₀ = some h ∧ HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h

/-- After `HintBitUnpack`: the result 1 and the hint stored, or 0 if it is malformed. -/
def H1 (s : State) : Prop :=
  Ctx (YV p) s₀ s ∧ ((accV s₀ s = 1 ∧ HOk p s₀ s) ∨ (accV s₀ s = 0 ∧ hOf p s₀ = none))

/-- The postcondition, at the end. -/
def VFin (s : State) : Prop :=
  Ctx (YV p) s₀ s ∧ ((accV s₀ s = 1 ∧ ∃ b, Spec.MlDsa.verifyMu p b (vPk p s₀) (vMu s₀) (vSig p s₀) = some true) ∨
    (accV s₀ s = 0 ∧ Spec.MlDsa.verifyMu p Spec.MlDsa.minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true))

end

theorem keepHint {p : Params} {s₀ : State} (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : (YV p).apart (hB p.k) bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    {h : List (Vector Bool Spec.MlDsa.n)} (hh : HintIs m (Buf.addr s₀ (hB p.k)) p.k h) :
    HintIs m' (Buf.addr s₀ (hB p.k)) p.k h :=
  Proof.MlDsa.Verify.hintIs_congr (fun i hi => Top.keep hp (stkV hN) hs fr i (by show i < 256 * p.k * 4; omega)) hh

theorem HOk.keep {p : Params} {s₀ s s' : State} (h : HOk p s₀ s) (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (YV p).apart (hB p.k) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    HOk p s₀ s' := by
  obtain ⟨hh, e, hi⟩ := h
  exact ⟨hh, e, keepHint hp hN hs fr hi⟩

theorem acc_keepV {p : Params} {s₀ s s' : State} (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (YV p).apart (sb oACC 4) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    accV s₀ s' = accV s₀ s :=
  keepW hp (stkV hN) hs fr

theorem acc_write {p : Params} {s₀ : State} (m : Mem) (v : BitVec 32) :
    (m.writeW (Buf.addr s₀ (accB (YV p))) v).readW (Buf.addr s₀ (sb oACC 4)) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem hint_piece : VP p (Ctx (YV p)) (H1 p) (hint P p) := by
  unfold hint
  refine Piece.seq (B := fun s₀ s => Ctx (YV p) s₀ s ∧ ((s.gpr .eax = 1 ∧ HOk p s₀ s) ∨
      (s.gpr .eax = 0 ∧ hOf p s₀ = none)))
    (hu_piece hP.hintUnpack 2 (oHint p) p.ω p.k vS (oP 0) hF.hint (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h)
      (fun s₀ s₀' s s' hp hp' hq h h' => by
        rw [sig_slice hF hp h (by lv hF), sig_slice hF hp' h' (by lv hF), (inputs_pub hq).2.2])
      fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩) ?_
  · rw [sig_slice hF hp h (by lv hF)] at post
    change (match vHint p (vSig p s₀) with
      | some hint => s'.gpr .eax = 1 ∧ HintIs s'.mem (Buf.addr s₀ (hB p.k)) p.k hint
      | none => s'.gpr .eax = 0) at post
    cases e : vHint p (vSig p s₀) with
    | none => rw [e] at post; exact .inr ⟨post, e⟩
    | some hh => rw [e] at post; exact .inl ⟨post.1, hh, e, post.2⟩
  refine stAcc_piece (Y := YV p) (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
    fun s₀ s s' hp h h' g m' => ⟨h', ?_⟩
  have ea : accV s₀ s' = s.gpr .eax := by rw [accV, m', acc_write]
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := YV p)
  rcases h.2 with ⟨e, ho⟩ | ⟨e, hn⟩
  · exact .inl ⟨by rw [ea, e], ho.keep hp (N := 0) (by omega) (by lv hF) fr⟩
  · exact .inr ⟨by rw [ea, e], hn⟩

end

/-! ## `z` -/

section
variable (p : Params) (s₀ : State)

/-- The first `i` norms of `z` are within the bound. -/
abbrev NormsOk (i : Nat) : Prop := ∀ j < i, normRq [toRq (vZ p (vSig p s₀) j)] < p.γ₁ - p.β

/-- After the first `i` entries of `z`. -/
structure ZI (i : Nat) (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  hint : HOk p s₀ s
  z : ∀ j < i, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (vSig p s₀) j))
  acc : accV s₀ s = if NormsOk p s₀ i then 1 else 0

end

theorem ZI.keep {p : Params} {i : Nat} {s₀ s s' : State} (h : ZI p s₀ i s) (hp : TPre (YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true) (sa : (YV p).apart (sb oACC 4) bs = true)
    (sz : ∀ j < i, (YV p).apart (pZ j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YV p) s₀ s') : ZI p s₀ i s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (stkV hN) (sz j hj) fr (h.z j hj),
    by rw [acc_keepV hp hN sa fr]; exact h.acc⟩

theorem ite_and_ite {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : BitVec 32) &&& (if Q then 1 else 0)) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem normsOk_succ {p : Params} {s₀ : State} {i : Nat} :
    (NormsOk p s₀ i ∧ normRq [toRq (vZ p (vSig p s₀) i)] < p.γ₁ - p.β) ↔ NormsOk p s₀ (i + 1) := by
  constructor
  · rintro ⟨h₁, h₂⟩ j hj
    rcases (by omega : j < i ∨ j = i) with hj | rfl
    exacts [h₁ j hj, h₂]
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem zOne_piece {i : Nat} (hi : i < p.ℓ) : VP p (ZI p · i) (ZI p · (i + 1)) (zOne P p i) := by
  have hzr := mul_row (a := lenZ p) hi
  unfold zOne
  refine Piece.seq (B := fun s₀ s => ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (vSig p s₀) i)))
    (bu_piece hP.bitUnpack 2 (p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ vS (oP (8 + i)) hF.bp.1 hF.bp.2
      (by lv hF) (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨h.keep hp (N := 80) (by omega) (by lv hF) (by lv hF)
        (fun j hj => by lv hF) fr h', ?_⟩) ?_
  · rw [sig_slice hF hp h.ctx (by lv hF)] at post
    exact post
  refine Piece.seq (B := fun s₀ s => (ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (vSig p s₀) i))) ∧
      s.gpr .eax = if normRq [toRq (vZ p (vSig p s₀) i)] < p.γ₁ - p.β then 1 else 0)
    (normLt_piece hP.normLt vS (oP (8 + i)) (p.γ₁ - p.β) hF.beta.2 (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩)
      fun s₀ s s' hp h h' fr e => ⟨⟨h.1.keep hp (N := 80) (by omega) (by lv hF) (by lv hF)
        (fun j hj => by lv hF) fr h', keepPolyD hp (stkV (by omega)) (by lv hF) fr h.2⟩, ?_⟩) ?_
  · rw [e, h.2.2]
  refine accAnd_piece (Y := YV p) (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1.ctx)
    fun s₀ s s' hp h h' m' => ?_
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := YV p)
  obtain ⟨⟨hz, hzi⟩, he⟩ := h
  refine ⟨h', hz.hint.keep hp (N := 0) (by omega) (by lv hF) fr, fun j hj => ?_, ?_⟩
  · rcases (by omega : j < i ∨ j = i) with hj | rfl
    · have : (YV p).apart (pZ j) [sb oACC 4] = true := by lv hF
      exact keepPolyD hp (stkV (by omega)) this fr (hz.z j hj)
    · have : (YV p).apart (pZ j) [sb oACC 4] = true := by lv hF
      exact keepPolyD hp (stkV (by omega)) this fr hzi
  · rw [accV, m', acc_write, accB_YV, ← accV, hz.acc, he, ite_and_ite]
    exact ite_congr (propext normsOk_succ) (fun _ => rfl) (fun _ => rfl)

end

end VG.Proof.MlDsa.X86.Verify
