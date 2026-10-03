import VerifiedGarbage.Proof.MlDsa.X86.Verify.Compute

/-!
# ML-DSA verification on x86 (32-bit): a row of `w′₁`

Row `r`, step by step, with what the temporaries hold (`RI`): `w′ = Σₛ Â[r, s]
ẑ[s]` (`dotAcc`), `t₁[r]` unpacked and its NTT, `ĉ t̂₁[r]`, `w′ = NTT⁻¹(… - ĉ
t̂₁[r])` (`wRow`), its `UseHint`s with `h[r]` (`w1Row`), and their
`SimpleBitPack` to row `r` of `w1Encode(w′₁)` (`row_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (callP)
open VG.Spec.MlDsa (Params Poly IPoly PolyIs NatPolyIs Reduced polyAt toRq ntt nttInv HintIs simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ vHint zHat dotAcc t1Hat wRow w1Row vT1)
open VG.Spec.Sha3 (bytesAt)

/-- In row `r`, with the facts `Q` about the temporaries. -/
def RI (p : Params) (r : Nat)
    (Q : List (Vector Bool Spec.MlDsa.n) → (Nat → Nat → Poly) → Poly → State → Mem → Prop) (s₀ s : State) : Prop :=
  ∃ h A C, CX p s₀ h A C p.ℓ true r s ∧ Q h A C s₀ s.mem

theorem CX.zh {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {cd : Bool}
    {nr : Nat} {s₀ s : State} (hc : CX p s₀ h A C p.ℓ cd nr s) {i : Nat} (hi : i < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (pZ i)) (zHat p (vSig p s₀) i) := by
  have e := hc.z i hi
  simp only [hi, ite_true] at e
  exact e

theorem CX.ch {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j nr : Nat}
    {s₀ s : State} (hc : CX p s₀ h A C j true nr s) : PolyIs s.mem (Buf.addr s₀ pC) (ntt C) := by
  have e := hc.c
  simp only [ite_true] at e
  exact e

theorem natPoly_le {m : Mem} {a : Addr} {f : Vector Nat Spec.MlDsa.n} (h : NatPolyIs m a f) {b : Nat}
    (hb : ∀ i (hi : i < Spec.MlDsa.n), f[i] ≤ b) : ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt m a i).toNat ≤ b :=
  fun i hi => by
    have e := congrArg (·[i]'hi) h
    simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn] at e
    rw [e]; exact hb i hi

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

theorem mulW_row : VP p (CI p · p.ℓ true r)
    (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r 1))
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pW, .buf (pA r 0), .buf (pZ 0)]) := by
  have hl := hF.l
  refine mul_piece (Y := YV p) _ _ _ _ _ _ hP.mul (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h⟩ => ⟨h.ctx, (h.a r hr 0 (by omega)).1, (h.zh (by omega)).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [(h.a r hr 0 (by omega)).2, (h.zh (by omega)).2] at out
  show PolyIs _ _ (Spec.MlDsa.add Spec.MlDsa.zero _)
  rw [Proof.MlDsa.Verify.add_zero_left]
  exact out

theorem mulAddW_row {j : Nat} (hj : j < p.ℓ) :
    VP p (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r j))
      (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r (j + 1)))
      (mulAddS P r j) := by
  have hl := hF.l
  refine mulAdd_piece (Y := YV p) _ _ _ _ _ _ hP.mulAdd (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1, (h.a r hr j hj).1, (h.zh hj).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [hw.2, (h.a r hr j hj).2, (h.zh hj).2] at out
  exact out

theorem t1_row : VP p (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ))
    (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) ((vT1 (vPk p s₀) r).map fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)))
    (callP vS "vg_mldsa_unpack_t1" P.unpackT1 [.buf ⟨0, 32 + 320 * r, 320⟩, .buf pT]) :=
  t1_piece (Y := YV p) hP.unpackT1 0 (32 + 320 * r) vS (oP 16) (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _⟩ => h.ctx)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (stkV (by omega)) (by lv hF) fr hw, by rw [pk_slice hF hp h.ctx (by lv hF)] at out; exact out⟩

theorem nttT_row : VP p (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) ((vT1 (vPk p s₀) r).map fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)))
    (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) (t1Hat (vPk p s₀) r))
    (nttAt P pT) :=
  inPlace_piece (Y := YV p) hP.ntt vS (oP 16) vS oSS (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (stkV (by omega)) (by lv hF) fr hw, by rw [ht.2] at out; exact out⟩

theorem mulT_row : VP p (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT) (t1Hat (vPk p s₀) r))
    (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r)))
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pT2, .buf pC, .buf pT]) :=
  mul_piece (Y := YV p) _ _ _ _ _ _ hP.mul (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, _, ht⟩ => ⟨h.ctx, h.ch.1, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h',
      keepPolyD hp (stkV (by omega)) (by lv hF) fr hw, by rw [h.ch.2, ht.2] at out; exact out⟩

theorem sub_row : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r)))
    (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub (dotAcc p (vSig p s₀) A r p.ℓ)
      (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r))))
    (callP vS "vg_mldsa_sub" P.sub [.buf pW, .buf pT2]) :=
  acc_piece (Y := YV p) hP.sub _ _ _ _ (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw, ht⟩ => ⟨h.ctx, hw.1, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by rw [hw.2, ht.2] at out; exact out⟩

theorem inv_rowV : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub
      (dotAcc p (vSig p s₀) A r p.ℓ) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r))))
    (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (vPk p s₀) (vSig p s₀) A (ntt C) r))
    (callP vS "vg_mldsa_inv_ntt" P.invNtt [.buf pW, .buf (ssB 1024)]) :=
  inPlace_piece (Y := YV p) hP.invNtt vS (oP 18) vS oSS (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by rw [hw.2] at out; exact out⟩

omit hP in
theorem addr_pB {s₀ : State} (hp : TPre (YV p) s₀) :
    Buf.addr s₀ (pB r) = Buf.addr s₀ (hB p.k) + BitVec.ofNat 64 (1024 * r) := by
  rw [Buf.addr_eq hp (b := pB r) (by lv hF), Buf.addr_eq hp (b := hB p.k) (by lv hF), BitVec.add_assoc,
    ← BitVec.ofNat_add]
  simp only [oP]

theorem hint_row : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (vPk p s₀) (vSig p s₀) A (ntt C) r))
    (RI p r fun h A C s₀ m => NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r))
    (callP vS "vg_mldsa_use_hint" P.useHint [.buf (pB r), .buf pW, .imm p.γ₂, .buf pW1]) :=
  useHint_piece (Y := YV p) hP.useHint vS (oP r) vS (oP 18) p.γ₂ vS (oP 19) hF.g2 (by lv hF)
    (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega)
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h', by
        have e := addr_pB hF hr hp
        simp only [pB, sb] at e
        rw [hw.2, e, Proof.MlDsa.Verify.hintAt_row h.hint hr] at out
        exact out⟩

theorem pack_row : VP p (RI p r fun h A C s₀ m =>
      NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r))
    (CI p · p.ℓ true (r + 1))
    (callP vS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf pW1, .imm (w1Max p), .buf (sb (oB + w1Len p * r) (w1Len p)), .imm (w1Len p)]) := by
  have hwr := w_row hr
  refine sbp_piece (Y := YV p) hP.simpleBitPack vS (oP 19) (w1Max p) vS (oB + w1Len p * r) (w1Len p) hF.sbp.1
    hF.sbp.2 (by lv hF) (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, natPoly_le hw fun i hi => by
      simp only [w1Row, Vector.getElem_zipWith]
      exact Proof.MlDsa.Verify.useHint_le hF.g2 _ _⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, ?_⟩
  have hc := h.keep hp (N := 80) (by omega) (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lv hF) (by lv hF) fr h'
  refine ⟨hc.ctx, hc.norms, hc.hh, hc.hint, hc.a, hc.z, hc.c, hc.gc, fun r' hr' => ?_⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · have := w_rows hr' (Nat.le_of_lt hr)
    rw [keepBytes hp (stkV (by omega)) (by lv hF) fr]; exact h.w r' hr'
  · rw [hw] at out; exact out

theorem row_piece : VP p (CI p · p.ℓ true r) (CI p · p.ℓ true (r + 1)) (row P p r) := by
  have hl := hF.l
  unfold row
  refine (mulW_row hP hF hr).seq ?_
  refine Piece.seq (B := RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ))
    ((seqR_piece (I := fun j => RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r j))
      (p.ℓ - 1) 1 fun j _ hj => mulAddW_row hP hF hr (by omega)).mono (fun _ _ _ h => h)
      fun _ _ _ h => by rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h) ?_
  exact (t1_row hP hF hr).seq ((nttT_row hP hF hr).seq ((mulT_row hP hF hr).seq ((sub_row hP hF hr).seq
    ((inv_rowV hP hF hr).seq ((hint_row hP hF hr).seq (pack_row hP hF hr))))))

end

end VG.Proof.MlDsa.X86.Verify
