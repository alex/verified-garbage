import VerifiedGarbage.Proof.MlKem.X86.EncRow

/-!
# ML-KEM on x86 (32-bit): the ciphertext of K-PKE.Encrypt

The end of row `i` (`row_piece`): `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`,
compressed into the ciphertext. Then `v` (`v_piece`): the products `t̂[j] ×_T
ŷ[j]`, with `t̂[j]` decoded from `ek` (`term0_piece`, `term_piece`), summed,
`NTT⁻¹`, `e₂` and `μ` added, and `v` compressed into the ciphertext. `encrypt`
takes the inputs (`Base`) to `Done` (`encrypt_piece`): if `eACC` is 1, the
ciphertext is K-PKE.Encrypt's for the matrix `aE` sampled (`ct_eq`), each of
whose entries was sampled within some bound (`samples`); if 0, one sample
failed within `minIterations`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

/-! ## The end of a row -/

/-- `NTT⁻¹` of `u[i]` is computed. -/
structure S7 (L : KemLay) (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * i + L.p.k) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = nttInv (partU L I s₀ i L.p.k))

/-- `u[i]` is computed. -/
structure S8 (L : KemLay) (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * i + L.p.k) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = KPke.encU L.p (aE L I s₀) (rE I s₀) i)

/-- The facts of the layout that the end of a row uses. -/
class RowOK (L : KemLay) : Prop where
  row : ∀ {Y : Lay}, SOK L Y →
    safe L Y [bU L Y.sc, bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc, bNS L Y.sc] = true ∧
    safe L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bE L Y.sc] = true ∧
    Y.apart (bU L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bE L Y.sc] = true ∧
    Y.apart (bACC L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bE L Y.sc] = true ∧
    safe L Y [bU L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc] = true ∧
    (Y.okW (bU L Y.sc) && Y.okW (bNS L Y.sc) && Y.sep (bU L Y.sc) (bNS L Y.sc)) = true ∧
    (Y.ok (bPRF L Y.sc) && Y.okW (bE L Y.sc) && Y.sep (bPRF L Y.sc) (bE L Y.sc)) = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (bE L Y.sc) && Y.sep (bU L Y.sc) (bE L Y.sc)) = true ∧
    (∀ i < L.p.k, (Y.ok (bU L Y.sc) && Y.okW (bCU L Y.sc i) && Y.sep (bU L Y.sc) (bCU L Y.sc i)) = true ∧
      safeS L Y [bCU L Y.sc i] = true ∧ Y.apart (bACC L Y.sc) [bCU L Y.sc i] = true ∧
      ∀ i' < i, Y.apart (bCU L Y.sc i') [bCU L Y.sc i] = true)

/-- Row `i`: `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into the ciphertext. -/
theorem row_piece [CeOK L] [BaseOK L] [EntOK L] [RowOK L] (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (B L Y I (L.p.k * i) i) (B L Y I (L.p.k * (i + 1)) (i + 1)) (encRow L Y.sc i) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, o₁, o₂, o₃, o₄⟩ := RowOK.row hS
  obtain ⟨c₁, c₂, c₃, c₄⟩ := o₄ i hi
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine entries_piece hS hρ i hi ?_ |>.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := S7 L Y I i) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc L.eU Y.sc
    L.eNS o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.u (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp hS.le r₁ (by omega) fr h'
    have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le r₂ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.u (by omega)).2 (ea ▸ e₁)]
  refine Piece.seq (cbd_piece hS (L.p.k + i) L.eE (Q := S7 L Y I i) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ?_) o₂) ?_
  · have k := h.toB.keep hp k88 r₃ (by omega) fr c
    have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp k88 r₅ fr
    refine ⟨k, keepRed hp k88 r₄ fr h.u.1, fun e₁ => ?_⟩
    rw [polyAt_congr (Top.keep hp k88 r₄ fr)]; exact h.u.2 (ea ▸ e₁)
  refine Piece.seq (B := S8 L Y I i) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eE o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.u.1, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.1.toB.keep hp hS.le r₆ (by omega) fr h'
    have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le r₇ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, h.1.u.2 (ea ▸ e₁), h.2.2]
    rfl
  refine ceK_piece (Y := Y) L.p.du (.inl rfl) Y.sc L.eU Y.sc (L.eC + 32 * L.p.du * i) c₁ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := keepS hp hS.le c₂ fr h' h.toBase h.y
  have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le c₃ fr
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp hS.le (c₄ i' hi') fr]; exact h.c (ea ▸ e₁) i' hi'
  · rw [post, h.u.2 (ea ▸ e₁)]

/-! ## `v` -/

section
variable (L : KemLay) (I : Inp) (s₀ : State)
/-- `t̂[0] ×_T ŷ[0] + … + t̂[j - 1] ×_T ŷ[j - 1]`. -/
abbrev partV (j : Nat) : Poly := KPke.dotK (ekT (I.ek s₀)) (yE I s₀) j
end

/-- Before term `j` of `v`: and `v` so far, if `0 < j`. -/
structure V (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  v : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧ polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = partV I s₀ j

/-- After `t̂[j]` is decoded. -/
structure V1 (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends V L Y I j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (bT L Y.sc)) (ekT (I.ek s₀) j)

/-- After `t̂[j] ×_T ŷ[j]` is computed, for `0 < j`. -/
structure V2 (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends V L Y I j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (bP L Y.sc)) (multiplyNTTs (ekT (I.ek s₀) j) (yE I s₀ j))

theorem V.keep {I : Inp} {j : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe L Y bs = true) (hU : Y.apart (bU L Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : V L Y I j s₀ s) (c : Ctx Y s₀ s') : V L Y I j s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, fun hj =>
    ⟨keepRed hp hM hU fr (h.v hj).1, by rw [polyAt_congr (Top.keep hp hM hU fr)]; exact (h.v hj).2⟩⟩

/-- The facts of the layout that `v` uses. -/
class VOK (L : KemLay) : Prop where
  v : ∀ {Y : Lay}, SOK L Y →
    safe L Y [bT L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bT L Y.sc] = true ∧
    safe L Y [bU L Y.sc, bNS L Y.sc] = true ∧ safe L Y [bP L Y.sc, bNS L Y.sc] = true ∧
    safe L Y [bU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bP L Y.sc, bNS L Y.sc] = true ∧
    Y.apart (bT L Y.sc) [bP L Y.sc, bNS L Y.sc] = true ∧
    (∀ j < L.p.k, (Y.ok ⟨Y.sc, L.eEK + 384 * j, 384⟩ && Y.okW (bT L Y.sc) &&
      Y.sep ⟨Y.sc, L.eEK + 384 * j, 384⟩ (bT L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (bT L Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (bNS L Y.sc) &&
      Y.sep (bU L Y.sc) (bT L Y.sc) && Y.sep (bU L Y.sc) (bY Y.sc 0) && Y.sep (bU L Y.sc) (bNS L Y.sc) &&
      Y.sep (bT L Y.sc) (bNS L Y.sc) && Y.sep (bY Y.sc 0) (bNS L Y.sc)) = true ∧
    (∀ j < L.p.k, (Y.okW (bP L Y.sc) && Y.ok (bT L Y.sc) && Y.ok (bY Y.sc j) && Y.okW (bNS L Y.sc) &&
      Y.sep (bP L Y.sc) (bT L Y.sc) && Y.sep (bP L Y.sc) (bY Y.sc j) && Y.sep (bP L Y.sc) (bNS L Y.sc) &&
      Y.sep (bT L Y.sc) (bNS L Y.sc) && Y.sep (bY Y.sc j) (bNS L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (bP L Y.sc) && Y.sep (bU L Y.sc) (bP L Y.sc)) = true
  w : ∀ {Y : Lay}, SOK L Y →
    safe L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bE L Y.sc] = true ∧
    Y.apart (bU L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bE L Y.sc] = true ∧
    safe L Y [bMU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bMU L Y.sc] = true ∧
    (Y.ok (bM L Y.sc) && Y.okW (bMU L Y.sc) && Y.sep (bM L Y.sc) (bMU L Y.sc)) = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (bMU L Y.sc) && Y.sep (bU L Y.sc) (bMU L Y.sc)) = true ∧
    (Y.ok (bU L Y.sc) && Y.okW ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ &&
      Y.sep (bU L Y.sc) ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩) = true ∧
    safe L Y [⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩] = true
  ct : ∀ {Y : Lay}, SOK L Y → Y.ok ⟨Y.sc, L.eC, 32 * L.p.du * L.p.k⟩ = true ∧
    Y.ok ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ = true

/-- `ek[384j : 384j + 384]`. -/
theorem ekT_eq [EntOK L] [VOK L] (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base L Y I s₀ s) {j : Nat}
    (hj : j < L.p.k) :
    decode12 (bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * j, 384⟩) 384) = ekT (I.ek s₀) j := by
  have hok := ((VOK.v hS).2.2.2.2.2.2.2.1 j hj)
  simp only [Bool.and_eq_true] at hok
  rw [ekT, ← h.ek, bytesAt_slice _ _ (show 384 * j + 384 ≤ L.p.ekLen by unfold Params.ekLen; omega),
    Buf.addr_eq hp (b := bEK L Y.sc) (EntOK.seed hS).2.1, Buf.addr_eq hp (b := ⟨Y.sc, L.eEK + 384 * j, 384⟩) hok.1.1,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `t̂[j]`, decoded, then `c`. -/
theorem dec_piece [EntOK L] [VOK L] (hS : SOK L Y) {I : Inp} (j : Nat) (hj : j < L.p.k)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (V1 L Y I j) Q c) :
    Piece (TPre Y) (TPub Y lk) (V L Y I j) Q
      (.seq (dec12C Y.sc ⟨Y.sc, L.eEK + 384 * j, 384⟩ (bT L Y.sc)) c) := by
  obtain ⟨v₁, v₂, -, -, -, -, -, v₈, -, -, -⟩ := VOK.v hS
  exact Piece.seq (dec12C_piece (Y := Y) Y.sc (L.eEK + 384 * j) Y.sc L.eT (v₈ j hj) hS.le (by sc_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp hS.le v₁ v₂ fr h', by rw [ekT_eq hS hp h.toBase hj] at post; exact post⟩) hc

/-- Term 0 of `v`: `v ← t̂[0] ×_T ŷ[0]`. -/
theorem term0_piece [EntOK L] [VOK L] (hS : SOK L Y) {I : Inp} (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (V L Y I 0) (V L Y I 1) (encTerm L Y.sc 0) := by
  obtain ⟨-, -, v₃, -, -, -, -, -, v₉, -, -⟩ := VOK.v hS
  refine dec_piece hS 0 hk (mulC_piece (Y := Y) Y.sc L.eU Y.sc L.eT Y.sc 0 Y.sc L.eNS v₉
    hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y 0 hk).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  refine ⟨h.toB.keep hp hS.le v₃ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, h.t.2, (h.y 0 hk).2]
  rfl

/-- Term `j + 1` of `v`: `v ← v + t̂[j + 1] ×_T ŷ[j + 1]`. -/
theorem term_piece [EntOK L] [VOK L] (hS : SOK L Y) {I : Inp} (j : Nat) (hj : j + 1 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (V L Y I (j + 1)) (V L Y I (j + 2)) (encTerm L Y.sc (j + 1)) := by
  obtain ⟨-, -, -, v₄, v₅, v₆, -, -, -, v₁₀, v₁₁⟩ := VOK.v hS
  refine dec_piece hS (j + 1) hj (.seq (B := V2 L Y I (j + 1))
    (mulC_piece (Y := Y) Y.sc L.eP Y.sc L.eT Y.sc (1024 * (j + 1)) Y.sc L.eNS (v₁₀ (j + 1) hj) hS.le
      (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · refine ⟨h.keep hp hS.le v₄ v₆ fr h', ?_⟩
    rw [h.t.2, (h.y (j + 1) (by omega)).2] at post; exact post
  refine accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eP v₁₁ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.v (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h.toB.keep hp hS.le v₅ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.v (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(t̂ ∘ ŷ)`, then with `e₂`, then with `μ`: `v`. -/
structure W (L : KemLay) (Y : Lay) (I : Inp) (n : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (bU L Y.sc)) (if n = 0 then nttInv (partV I s₀ L.p.k)
    else if n = 1 then add (nttInv (partV I s₀ L.p.k)) (cbd (rE I s₀) (2 * L.p.k))
    else KPke.encV L.p (I.ek s₀) (I.m s₀) (rE I s₀))

/-- After `v` is compressed into the ciphertext. -/
structure Done (L : KemLay) (Y : Lay) (I : Inp) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  cv : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩) (32 * L.p.dv) =
    compressEncode L.p.dv (KPke.encV L.p (I.ek s₀) (I.m s₀) (rE I s₀))

/-- `v`, compressed into the ciphertext. -/
theorem v_piece [CeOK L] [BaseOK L] [EntOK L] [RowOK L] [VOK L] (hS : SOK L Y) {I : Inp} (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (B L Y I (L.p.k * L.p.k) L.p.k) (Done L Y I) (Impl.MlKem.X86.encV L Y.sc) := by
  obtain ⟨r₁, -, -, -, -, r₆, -, o₁, o₂, o₃, -⟩ := RowOK.row hS
  obtain ⟨w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈⟩ := VOK.w hS
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine (Piece.seqs0 (P := V L Y I) L.p.k (fun j hj => match j, hj with
    | 0, _ => term0_piece hS hk
    | j + 1, hj => term_piece hS j hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := W L Y I 0) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc L.eU Y.sc
    L.eNS o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.v hk).1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h.toB.keep hp hS.le r₁ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [(h.v hk).2] at post; exact post
  refine Piece.seq (cbd_piece hS (2 * L.p.k) L.eE (Q := W L Y I 0) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ⟨h.toB.keep hp k88 w₁ (Nat.le_refl _) fr c, polyIs_congr (Top.keep hp k88 w₂ fr) h.v⟩)
    o₂) ?_
  refine Piece.seq (B := W L Y I 1) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eE o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  refine Piece.seq (B := fun s₀ s => W L Y I 1 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ (bMU L Y.sc)) (decodeDecompress 1 (I.m s₀)))
    (ddC_piece (Y := Y) dd768 1 (by decide) Y.sc L.eM Y.sc L.eMU w₅ hS.le (by sc_taint) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨⟨h.toB.keep hp hS.le w₃ (Nat.le_refl _) fr h',
        polyIs_congr (Top.keep hp hS.le w₄ fr) h.v⟩, by rw [h.m] at post; exact post⟩) ?_
  refine Piece.seq (B := W L Y I 2) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eMU w₆ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  exact ceK_piece (Y := Y) L.p.dv (.inr rfl) Y.sc L.eU Y.sc (L.eC + 32 * L.p.du * L.p.k) w₇ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.toB.keep hp hS.le w₈ (Nat.le_refl _) fr h', by rw [post, h.v.2]; rfl⟩

/-! ## K-PKE.Encrypt -/

/-- `encrypt`, from its inputs. -/
theorem encrypt_piece [CeOK L] [BaseOK L] [YOK L] [EntOK L] [RowOK L] [VOK L] (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (Base L Y I) (Done L Y I) (encrypt L Y.sc) :=
  ys_piece hS <| (Piece.seqs0 (P := fun i => B L Y I (L.p.k * i) i) L.p.k (fun i hi => row_piece hS hρ i hi)
    (v_piece hS hk)).mono (fun _ _ _ h => ⟨h.toBase, h.y, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

/-- The ciphertext, if every sample succeeded. -/
theorem ct_eq [VOK L] (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Done L Y I s₀ s)
    (e : accE L Y s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ (bC L Y.sc)) L.p.ctLen = KPke.ct L.p (aE L I s₀) (I.ek s₀) (I.m s₀) (rE I s₀) := by
  obtain ⟨o₁, o₂⟩ := VOK.ct hS
  rw [bytes_split hp _ (o' := L.eC + 32 * L.p.du * L.p.k) (l₁ := 32 * L.p.du * L.p.k) (l₂ := 32 * L.p.dv) rfl
    (by rw [Params.ctLen, Nat.mul_add, Nat.mul_assoc]) o₁ o₂, bytes_catK hp _ o₁, h.cv, KPke.ct]
  exact congrArg (· ++ _) (catK_congr fun i hi => h.c e i hi)

/-- Every sample, within one bound. -/
theorem samples {I : Inp} {s₀ s : State} (h : Done L Y I s₀ s) (e : accE L Y s₀ s = 1) :
    ∃ M, ∀ i < L.p.k, ∀ j < L.p.k, sampleNTT M (matSeed (ρE L I s₀) i j) = some (aE L I s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range (L.p.k * L.p.k)).map fun k =>
      (mSE L I s₀ k, aE L I s₀ (k % L.p.k) (k / L.p.k))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mSE L I s₀ k) (sv (mSE L I s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mSE L I s₀ (L.p.k * j + i), aE L I s₀ ((L.p.k * j + i) % L.p.k) ((L.p.k * j + i) / L.p.k))
    (List.mem_map.mpr ⟨L.p.k * j + i, List.mem_range.mpr (idx_lt hj hi), rfl⟩)
  rw [mSE_eq I s₀ hi, idx_mod hi, idx_div hi] at r
  exact r

end VG.Proof.MlKem.X86.Enc
