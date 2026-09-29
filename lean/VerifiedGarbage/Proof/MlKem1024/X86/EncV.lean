import VerifiedGarbage.Proof.MlKem1024.X86.EncRow

/-!
# ML-KEM-1024 on x86 (32-bit): the ciphertext of K-PKE.Encrypt

Untrusted: everything here is checked by Lean. The end of row `i`
(`row_piece`): `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into the
ciphertext. Then `v` (`v_piece`): the products `t̂[j] ×_T ŷ[j]`, with `t̂[j]`
decoded from `ek` (`term0_piece`, `term_piece`), summed, `NTT⁻¹`, `e₂` and `μ`
added, and `v` compressed into the ciphertext. `encrypt` takes the inputs
(`Base`) to `Done` (`encrypt_piece`): if `eACC` is 1, the ciphertext is
K-PKE.Encrypt's for the matrix `aE` sampled (`ct_eq`), each of whose entries
was sampled within some bound (`samples`); if 0, one sample failed within
`minIterations`.
-/

namespace VG.Proof.MlKem1024.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte}

/-! ## The end of a row -/

/-- `NTT⁻¹` of `u[i]` is computed. -/
structure S7 (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop extends B Y I (4 * i + 4) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU Y.sc)) ∧
    (accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU Y.sc)) = nttInv (partU I s₀ i 4))

/-- `u[i]` is computed. -/
structure S8 (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop extends B Y I (4 * i + 4) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU Y.sc)) ∧
    (accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU Y.sc)) = encU1024 (aE I s₀) (rE I s₀) i)

theorem safe_row (hS : SOK Y) :
    safe Y [bU Y.sc, bNS Y.sc] = true ∧ Y.apart (bACC Y.sc) [bU Y.sc, bNS Y.sc] = true ∧
    safe Y [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bE Y.sc] = true ∧
    Y.apart (bU Y.sc) [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bE Y.sc] = true ∧
    Y.apart (bACC Y.sc) [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bE Y.sc] = true ∧
    safe Y [bU Y.sc] = true ∧ Y.apart (bACC Y.sc) [bU Y.sc] = true ∧
    (Y.okW (bU Y.sc) && Y.okW (bNS Y.sc) && Y.sep (bU Y.sc) (bNS Y.sc)) = true ∧
    (Y.ok (bPRF Y.sc) && Y.okW (bE Y.sc) && Y.sep (bPRF Y.sc) (bE Y.sc)) = true ∧
    (Y.okW (bU Y.sc) && Y.ok (bE Y.sc) && Y.sep (bU Y.sc) (bE Y.sc)) = true ∧
    (∀ i < 4, (Y.ok (bU Y.sc) && Y.okW (bCU Y.sc i) && Y.sep (bU Y.sc) (bCU Y.sc i)) = true ∧
      safeS Y [bCU Y.sc i] = true ∧ Y.apart (bACC Y.sc) [bCU Y.sc i] = true ∧
      ∀ i' < i, Y.apart (bCU Y.sc i') [bCU Y.sc i] = true) := by
  sc_decide'

/-- Row `i`: `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into the ciphertext. -/
theorem row_piece (hS : SOK Y) {I : Inp} (hρ : RhoPub Y lk I) (i : Nat) (hi : i < 4)
    {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (e4EK + 1568) i)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (e4KR + 64) (4 + i))) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax (bU Y.sc) ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 11))] : List Instr) ++ ptrTo Y.sc .edx (bCU Y.sc i) ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * 11)))] : List Instr))) h₃).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (B Y I (4 * i) i) (B Y I (4 * i + 4) (i + 1)) (enc4Row Y.sc i) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, o₁, o₂, o₃, o₄⟩ := safe_row hS
  obtain ⟨c₁, c₂, c₃, c₄⟩ := o₄ i hi
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (entry0_piece hS hρ i hi t₁ |>.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h) ?_
  refine Piece.seq (entry_piece hS hρ i 0 hi (by decide) t₁ (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (entry_piece hS hρ i 1 hi (by decide) t₁ (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (entry_piece hS hρ i 2 hi (by decide) t₁ (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (B := S7 Y I i) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc e4U Y.sc e4NS o₁
    hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.u (by decide)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp hS.le r₁ (by omega) fr h'
    have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le r₂ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.u (by decide)).2 (ea ▸ e₁)]
  refine Piece.seq (cbd_piece hS (4 + i) e4E (Q := S7 Y I i) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ?_) o₂ t₂ (by sc_taint)) ?_
  · have k := h.toB.keep hp k88 r₃ (by omega) fr c
    have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp k88 r₅ fr
    refine ⟨k, keepRed hp k88 r₄ fr h.u.1, fun e₁ => ?_⟩
    rw [polyAt_congr (Top.keep hp k88 r₄ fr)]; exact h.u.2 (ea ▸ e₁)
  refine Piece.seq (B := S8 Y I i) (accC_piece add_verified add_nosp add_stack Y.sc e4U Y.sc e4E o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.u.1, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.1.toB.keep hp hS.le r₆ (by omega) fr h'
    have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le r₇ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, h.1.u.2 (ea ▸ e₁), h.2.2]
    rfl
  refine ceC1024_piece (Y := Y) 11 (by decide) Y.sc e4U Y.sc (e4C + 352 * i) c₁ hS.le t₃
    (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := keepS hp hS.le c₂ fr h' h.toBase h.y
  have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le c₃ fr
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp hS.le (c₄ i' hi') fr]; exact h.c (ea ▸ e₁) i' hi'
  · rw [post, h.u.2 (ea ▸ e₁)]

/-! ## `v` -/

section
variable (I : Inp) (s₀ : State)
/-- `t̂[0] ×_T ŷ[0] + … + t̂[j - 1] ×_T ŷ[j - 1]`, for `0 < j`. -/
noncomputable def partV : Nat → Poly
  | 0 => zero
  | 1 => multiplyNTTs (ekT (I.ek s₀) 0) (yE I s₀ 0)
  | j + 1 => add (partV j) (multiplyNTTs (ekT (I.ek s₀) j) (yE I s₀ j))
end

/-- Before term `j` of `v`: and `v` so far, if `0 < j`. -/
structure V (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends B Y I 16 4 s₀ s where
  v : 0 < j → Reduced s.mem (Buf.addr s₀ (bU Y.sc)) ∧ polyAt s.mem (Buf.addr s₀ (bU Y.sc)) = partV I s₀ j

/-- After `t̂[j]` is decoded. -/
structure V1 (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends V Y I j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (bT Y.sc)) (ekT (I.ek s₀) j)

/-- After `t̂[j] ×_T ŷ[j]` is computed, for `0 < j`. -/
structure V2 (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends V Y I j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (bP Y.sc)) (multiplyNTTs (ekT (I.ek s₀) j) (yE I s₀ j))

theorem V.keep {I : Inp} {j : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe Y bs = true) (hU : Y.apart (bU Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : V Y I j s₀ s) (c : Ctx Y s₀ s') : V Y I j s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, fun hj =>
    ⟨keepRed hp hM hU fr (h.v hj).1, by rw [polyAt_congr (Top.keep hp hM hU fr)]; exact (h.v hj).2⟩⟩

theorem ok_ek (hS : SOK Y) : ∀ j < 4, Y.ok ⟨Y.sc, e4EK + 384 * j, 384⟩ = true := by sc_decide

/-- `ek[384j : 384j + 384]`. -/
theorem ekT_eq (hS : SOK Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base Y I s₀ s) {j : Nat} (hj : j < 4) :
    decode12 (bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, e4EK + 384 * j, 384⟩) 384) = ekT (I.ek s₀) j := by
  rw [ekT, ← h.ek, bytesAt_slice _ _ (show 384 * j + 384 ≤ 1568 by omega), Buf.addr_eq hp (b := bEK Y.sc) (by sc_decide),
    Buf.addr_eq hp (b := ⟨Y.sc, e4EK + 384 * j, 384⟩) (ok_ek hS j hj),
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem safe_v (hS : SOK Y) :
    safe Y [bT Y.sc] = true ∧ Y.apart (bU Y.sc) [bT Y.sc] = true ∧
    safe Y [bU Y.sc, bNS Y.sc] = true ∧ safe Y [bP Y.sc, bNS Y.sc] = true ∧ safe Y [bU Y.sc] = true ∧
    Y.apart (bU Y.sc) [bP Y.sc, bNS Y.sc] = true ∧ Y.apart (bT Y.sc) [bP Y.sc, bNS Y.sc] = true ∧
    (∀ j < 4, (Y.ok ⟨Y.sc, e4EK + 384 * j, 384⟩ && Y.okW (bT Y.sc) &&
      Y.sep ⟨Y.sc, e4EK + 384 * j, 384⟩ (bT Y.sc)) = true) ∧
    (Y.okW (bU Y.sc) && Y.ok (bT Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (bNS Y.sc) && Y.sep (bU Y.sc) (bT Y.sc) &&
      Y.sep (bU Y.sc) (bY Y.sc 0) && Y.sep (bU Y.sc) (bNS Y.sc) && Y.sep (bT Y.sc) (bNS Y.sc) &&
      Y.sep (bY Y.sc 0) (bNS Y.sc)) = true ∧
    (∀ j < 4, (Y.okW (bP Y.sc) && Y.ok (bT Y.sc) && Y.ok (bY Y.sc j) && Y.okW (bNS Y.sc) &&
      Y.sep (bP Y.sc) (bT Y.sc) && Y.sep (bP Y.sc) (bY Y.sc j) && Y.sep (bP Y.sc) (bNS Y.sc) &&
      Y.sep (bT Y.sc) (bNS Y.sc) && Y.sep (bY Y.sc j) (bNS Y.sc)) = true) ∧
    (Y.okW (bU Y.sc) && Y.ok (bP Y.sc) && Y.sep (bU Y.sc) (bP Y.sc)) = true := by
  sc_decide'

/-- `t̂[j]`, decoded, then `c`. -/
theorem dec_piece (hS : SOK Y) {I : Inp} (j : Nat) (hj : j < 4) {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨Y.sc, e4EK + 384 * j, 384⟩ ++ ptrTo Y.sc .ecx (bT Y.sc))) h₁).isSome = true)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (V1 Y I j) Q c) :
    Piece (TPre Y) (TPub Y lk) (V Y I j) Q
      (.seq (dec12C Y.sc ⟨Y.sc, e4EK + 384 * j, 384⟩ (bT Y.sc)) c) := by
  obtain ⟨v₁, v₂, -, -, -, -, -, v₈, -, -, -⟩ := safe_v hS
  exact Piece.seq (dec12C_piece (Y := Y) Y.sc (e4EK + 384 * j) Y.sc e4T (v₈ j hj) hS.le t₁
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp hS.le v₁ v₂ fr h', by rw [ekT_eq hS hp h.toBase hj] at post; exact post⟩) hc

/-- Term 0 of `v`: `v ← t̂[0] ×_T ŷ[0]`. -/
theorem term0_piece (hS : SOK Y) {I : Inp} :
    Piece (TPre Y) (TPub Y lk) (V Y I 0) (V Y I 1) (enc4Term Y.sc 0) := by
  obtain ⟨-, -, v₃, -, -, -, -, -, v₉, -, -⟩ := safe_v hS
  refine dec_piece hS 0 (by decide) (by sc_taint) (mulC_piece (Y := Y) Y.sc e4U Y.sc e4T Y.sc 0 Y.sc e4NS v₉
    hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y 0 (by decide)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  refine ⟨h.toB.keep hp hS.le v₃ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, h.t.2, (h.y 0 (by decide)).2]
  rfl

/-- Term `j + 1` of `v`: `v ← v + t̂[j + 1] ×_T ŷ[j + 1]`. -/
theorem term_piece (hS : SOK Y) {I : Inp} (j : Nat) (hj : j + 1 < 4) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨Y.sc, e4EK + 384 * (j + 1), 384⟩ ++ ptrTo Y.sc .ecx (bT Y.sc))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax (bP Y.sc) ++ ptrTo Y.sc .ecx (bT Y.sc) ++
      ptrTo Y.sc .edx (bY Y.sc (j + 1)) ++ ptrTo Y.sc .edi (bNS Y.sc))) h₂).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (V Y I (j + 1)) (V Y I (j + 2)) (enc4Term Y.sc (j + 1)) := by
  obtain ⟨-, -, -, v₄, v₅, v₆, -, -, -, v₁₀, v₁₁⟩ := safe_v hS
  refine dec_piece hS (j + 1) hj t₁ (.seq (B := V2 Y I (j + 1))
    (mulC_piece (Y := Y) Y.sc e4P Y.sc e4T Y.sc (1024 * (j + 1)) Y.sc e4NS (v₁₀ (j + 1) hj) hS.le t₂
      (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y (j + 1) (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_)
  · refine ⟨h.keep hp hS.le v₄ v₆ fr h', ?_⟩
    rw [h.t.2, (h.y (j + 1) (by omega)).2] at post; exact post
  refine accC_piece add_verified add_nosp add_stack Y.sc e4U Y.sc e4P v₁₁ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.v (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h.toB.keep hp hS.le v₅ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.v (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(t̂ ∘ ŷ)`, then with `e₂`, then with `μ`: `v`. -/
structure W (Y : Lay) (I : Inp) (n : Nat) (s₀ s : State) : Prop extends B Y I 16 4 s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (bU Y.sc)) (if n = 0 then nttInv (partV I s₀ 4)
    else if n = 1 then add (nttInv (partV I s₀ 4)) (cbd (rE I s₀) 8)
    else encV1024 (I.ek s₀) (I.m s₀) (rE I s₀))

/-- After `v` is compressed into the ciphertext. -/
structure Done (Y : Lay) (I : Inp) (s₀ s : State) : Prop extends B Y I 16 4 s₀ s where
  cv : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, e4C + 1408, 160⟩) 160 =
    compressEncode 5 (encV1024 (I.ek s₀) (I.m s₀) (rE I s₀))

theorem safe_w (hS : SOK Y) :
    safe Y [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bE Y.sc] = true ∧
    Y.apart (bU Y.sc) [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bE Y.sc] = true ∧
    safe Y [bMU Y.sc] = true ∧ Y.apart (bU Y.sc) [bMU Y.sc] = true ∧
    (Y.ok (bM Y.sc) && Y.okW (bMU Y.sc) && Y.sep (bM Y.sc) (bMU Y.sc)) = true ∧
    (Y.okW (bU Y.sc) && Y.ok (bMU Y.sc) && Y.sep (bU Y.sc) (bMU Y.sc)) = true ∧
    (Y.ok (bU Y.sc) && Y.okW ⟨Y.sc, e4C + 1408, 160⟩ && Y.sep (bU Y.sc) ⟨Y.sc, e4C + 1408, 160⟩) = true ∧
    safe Y [⟨Y.sc, e4C + 1408, 160⟩] = true := by
  sc_decide'

/-- `v`, compressed into the ciphertext. -/
theorem v_piece (hS : SOK Y) {I : Inp} :
    Piece (TPre Y) (TPub Y lk) (B Y I 16 4) (Done Y I) (enc4V Y.sc) := by
  obtain ⟨r₁, -, -, -, -, r₆, -, o₁, o₂, o₃, -⟩ := safe_row hS
  obtain ⟨w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈⟩ := safe_w hS
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (term0_piece hS |>.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h) ?_
  refine Piece.seq (term_piece hS 0 (by decide) (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (term_piece hS 1 (by decide) (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (term_piece hS 2 (by decide) (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (B := W Y I 0) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc e4U Y.sc e4NS o₁
    hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.v (by decide)).1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h.toB.keep hp hS.le r₁ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [(h.v (by decide)).2] at post; exact post
  refine Piece.seq (cbd_piece hS 8 e4E (Q := W Y I 0) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ⟨h.toB.keep hp k88 w₁ (Nat.le_refl _) fr c, polyIs_congr (Top.keep hp k88 w₂ fr) h.v⟩)
    o₂ (by sc_taint) (by sc_taint)) ?_
  refine Piece.seq (B := W Y I 1) (accC_piece add_verified add_nosp add_stack Y.sc e4U Y.sc e4E o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  refine Piece.seq (B := fun s₀ s => W Y I 1 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ (bMU Y.sc)) (decodeDecompress 1 (I.m s₀)))
    (ddC_piece (Y := Y) 1 (by decide) Y.sc e4M Y.sc e4MU w₅ hS.le (by sc_taint) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨⟨h.toB.keep hp hS.le w₃ (Nat.le_refl _) fr h',
        polyIs_congr (Top.keep hp hS.le w₄ fr) h.v⟩, by rw [h.m] at post; exact post⟩) ?_
  refine Piece.seq (B := W Y I 2) (accC_piece add_verified add_nosp add_stack Y.sc e4U Y.sc e4MU w₆ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  exact ceC1024_piece (Y := Y) 5 (by decide) Y.sc e4U Y.sc (e4C + 1408) w₇ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.toB.keep hp hS.le w₈ (Nat.le_refl _) fr h', by rw [post, h.v.2]; rfl⟩

/-! ## K-PKE.Encrypt -/

/-- `encrypt`, from its inputs. -/
theorem encrypt_piece (hS : SOK Y) {I : Inp} (hρ : RhoPub Y lk I) :
    Piece (TPre Y) (TPub Y lk) (Base Y I) (Done Y I) (encrypt4 Y.sc) :=
  ys_piece hS <| .seq (Piece.mono (row_piece hS hρ 0 (by decide) (by sc_taint) (by sc_taint) (by sc_taint))
    (fun _ _ _ h => ⟨h.toBase, h.y, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h) <|
  .seq (row_piece hS hρ 1 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) <|
  .seq (row_piece hS hρ 2 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) <|
  .seq (row_piece hS hρ 3 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) (v_piece hS)

/-- The ciphertext, if every sample succeeded. -/
theorem ct_eq (hS : SOK Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Done Y I s₀ s) (e : accE Y s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ (bC Y.sc)) 1568 = ct1024 (aE I s₀) (I.ek s₀) (I.m s₀) (rE I s₀) := by
  rw [bytes_split hp _ (o' := e4C + 1408) (l₁ := 1408) (l₂ := 160) rfl rfl (by sc_decide) (by sc_decide),
    bytes_split hp _ (o' := e4C + 1056) (l₁ := 1056) (l₂ := 352) rfl rfl (by sc_decide) (by sc_decide),
    bytes_split hp _ (o' := e4C + 704) (l₁ := 704) (l₂ := 352) rfl rfl (by sc_decide) (by sc_decide),
    bytes_split hp _ (o' := e4C + 352) (l₁ := 352) (l₂ := 352) rfl rfl (by sc_decide) (by sc_decide)]
  rw [show (⟨Y.sc, e4C, 352⟩ : Buf) = bCU Y.sc 0 from rfl, show (⟨Y.sc, e4C + 352, 352⟩ : Buf) = bCU Y.sc 1 from rfl,
    show (⟨Y.sc, e4C + 704, 352⟩ : Buf) = bCU Y.sc 2 from rfl,
    show (⟨Y.sc, e4C + 1056, 352⟩ : Buf) = bCU Y.sc 3 from rfl, h.c e 0 (by decide), h.c e 1 (by decide),
    h.c e 2 (by decide), h.c e 3 (by decide), h.cv]
  rfl

/-- Every sample, within one bound. -/
theorem samples {I : Inp} {s₀ s : State} (h : Done Y I s₀ s) (e : accE Y s₀ s = 1) :
    ∃ M, ∀ i < 4, ∀ j < 4, sampleNTT M (matSeed (ρE I s₀) i j) = some (aE I s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range 16).map fun k => (mSE I s₀ k, aE I s₀ (k % 4) (k / 4))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mSE I s₀ k) (sv (mSE I s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mSE I s₀ (4 * j + i), aE I s₀ ((4 * j + i) % 4) ((4 * j + i) / 4))
    (List.mem_map.mpr ⟨4 * j + i, List.mem_range.mpr (by omega), rfl⟩)
  rw [mSE_eq I s₀ hi, show (4 * j + i) % 4 = i by omega, show (4 * j + i) / 4 = j by omega] at r
  exact r

end VG.Proof.MlKem1024.X86.Enc
