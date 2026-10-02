import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestPack

/-!
# ML-DSA key generation on x86 (32-bit): the rows of `t`

Row `i` (`row_piece`): `t = Σⱼ Â[i, j] ŝ₁[j]` (`dotK`, a product then `ℓ - 1`
products added), `NTT⁻¹`, `s₂[i]` added (`tK`), `Power2Round`, and `t₁`
`SimpleBitPack`ed to `pk` and `t₀` `BitPack`ed to `sk`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv polyAt coeffAt Reduced PolyIs NatPolyIs bitPack
  simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- During row `i`: the keys so far, and `t` holding `v`. -/
abbrev RowT (p : Params) (i : Nat) (v : (Nat → Poly) → (Nat → IPoly) → Poly) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (tB p)) (v A S)

theorem KR.nttS {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {nr : Nat} {s₀ s : State}
    (h : KR p A S (p.ℓ + p.k) p.ℓ nr s₀ s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (sB p j)) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem t0_params : ((4095 : Nat), (4096 : Nat)) ∈ Spec.MlDsa.bitPackParams := by decide

theorem power2Round_fst' (c : Spec.MlDsa.Zq) : (power2Round c).1.toNat ≤ 1023 := by
  have := Proof.MlDsa.KeyGen.power2Round_fst c; omega

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_row : KP p (KRx p (p.ℓ + p.k) p.ℓ i) (RowT p i fun A S => dotK p A S i 1)
    (callP kS "vg_mldsa_multiply_ntt" P.mul [.buf (tB p), .buf (aB (p.ℓ * i)), .buf (sB p 0)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega
  refine mul_piece (Y := YK p) _ _ _ _ _ _ hP.mul (by layp hF [chk3]) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.aS _ he).1, (h.nttS (by omega)).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [(h.aS _ he).2, (h.nttS (by omega)).2, ← Proof.MlDsa.KeyGen.dotK_one] at out
  exact out

theorem mulAdd_row {j : Nat} (hj₁ : 1 ≤ j) (hj : j < p.ℓ) :
    KP p (RowT p i fun A S => dotK p A S i j) (RowT p i fun A S => dotK p A S i (j + 1)) (mulAddS P p i j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have he : p.ℓ * i + j < p.k * p.ℓ := by
    have : p.ℓ * (i + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega
  refine mulAdd_piece (Y := YK p) _ _ _ _ _ _ hP.mulAdd (by layp hF [chk3]) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.aS _ he).1, (h.nttS hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2, (h.aS _ he).2, (h.nttS hj).2, ← Proof.MlDsa.KeyGen.dotK_succ] at out
  exact out

theorem inv_row : KP p (RowT p i fun A S => dotK p A S i p.ℓ) (RowT p i fun A S => nttInv (dotK p A S i p.ℓ))
    (callP kS "vg_mldsa_inv_ntt" P.invNtt [.buf (tB p), .buf (ssB 1024)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine inPlace_piece (Y := YK p) hP.invNtt _ _ _ _ (by layp hF) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2] at out
  exact out

theorem add_row : KP p (RowT p i fun A S => nttInv (dotK p A S i p.ℓ)) (RowT p i fun A S => tK p A S i)
    (callP kS "vg_mldsa_add" P.add [.buf (tB p), .buf (sB p (p.ℓ + i))]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine acc_piece (Y := YK p) hP.add _ _ _ _ (by layp hF) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1, (h.s2 i hi).1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', ?_⟩
  rw [ht.2, (h.s2 i hi).2] at out
  exact out

/-- After `Power2Round` of row `i`. -/
abbrev RowP (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧ NatPolyIs s.mem (Buf.addr s₀ (t1B p)) (t1K p A S i) ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_row : KP p (RowT p i fun A S => tK p A S i) (RowP p i)
    (callP kS "vg_mldsa_power2round" P.power2Round [.buf (tB p), .buf (t1B p), .buf (t0B p)]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine p2r_piece (Y := YK p) _ _ _ _ _ _ hP.power2Round (by layp hF [chkP2]) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun s₀ s _ ⟨A, S, h, ht⟩ => ⟨h.ctx, ht.1⟩)
    fun s₀ s s' hp ⟨A, S, h, ht⟩ h' fr o₁ o₂ => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', ?_, ?_⟩
  · rw [ht.2] at o₁; exact o₁
  · rw [ht.2] at o₂; exact o₂

/-- After `t₁` is packed. -/
abbrev RowQ (p : Params) (i : Nat) (s₀ s : State) : Prop :=
  ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ i s₀ s ∧
    PolyIs s.mem (Buf.addr s₀ (t0B p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_row : KP p (RowP p i) (RowQ p i)
    (callP kS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf (t1B p), .imm 1023, .buf ⟨1, 32 + 320 * i, 320⟩, .imm 320]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine sbp_piece (Y := YK p) hP.simpleBitPack _ _ 1023 _ _ 320 (by decide) (by decide) (by layp hF)
    (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h1, _⟩ => ⟨h.ctx, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h1, h0⟩ h' fr out => ⟨A, S, h.keep hp (N := 80) (by omega) (by safeR hF)
      (fun _ _ => by layp hF) fr h', keepPolyD hp (stkN (by omega)) (by layp hF) fr h0, ?_⟩
  · have e := congrArg (fun v : Vector Nat 256 => v[j]'hj) h1
    simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn, t1K, Vector.getElem_map] at e
    rw [e]; exact power2Round_fst' _
  · rw [out, h1]

theorem bp_row : KP p (RowQ p i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (callP kS "vg_mldsa_bit_pack" P.bitPack
      [.buf (t0B p), .imm 4095, .imm 4096, .buf ⟨2, oT0 p + 416 * i, 416⟩, .imm 416]) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine bp_piece (Y := YK p) hP.bitPack _ _ 4095 4096 _ _ 416 t0_params (by decide) (by layp hF)
    (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, h0, _⟩ => ⟨h.ctx, h0.1, fun j hj => ?_⟩)
    fun s₀ s s' hp ⟨A, S, h, h0, hb⟩ h' fr out => ⟨A, S, ?_⟩
  · rw [coeff_val h0 hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd ((tK p A S i)[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    omega
  · have k := h.keep hp (N := 80) (by omega) (by safeR hF) (fun _ _ => by layp hF) fr h'
    refine { k with rows := fun i' hi' => ?_ }
    rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
    · exact k.rows i' hi'
    · refine ⟨by rw [keepBytes hp (stkN (by omega)) (by layp hF) fr]; exact hb, ?_⟩
      rw [out, h0.2, Vector.map_map]
      congr 1
      refine Vector.map_congr_left fun c _ => ?_
      have := Proof.MlDsa.KeyGen.power2Round_snd c
      exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem row_piece : KP p (KRx p (p.ℓ + p.k) p.ℓ i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (mul_row hP hF hi).seq (Piece.seq ?_ ((inv_row hP hF hi).seq ((add_row hP hF hi).seq
    ((p2r_row hP hF hi).seq ((sbp_row hP hF hi).seq (bp_row hP hF hi))))))
  refine Piece.mono (seqR_piece (I := fun j => RowT p i fun A S => dotK p A S i j) (p.ℓ - 1) 1
    fun j h1 h2 => mulAdd_row hP hF hi h1 (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

end

end VG.Proof.MlDsa.X86.KeyGen
