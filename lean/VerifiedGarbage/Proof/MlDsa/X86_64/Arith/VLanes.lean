import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VArith
import VerifiedGarbage.Proof.MlKem.X86_64.VLanes
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt

/-!
# ML-DSA on x86-64: coefficients in the doublewords of SSE registers

A register holds four coefficients (`DLanes`), and the butterflies `vbfly` and
`vibfly` compute four butterflies of the specification at once (`vbfly_ok`,
`vibfly_ok`), from `q` and `-q⁻¹` in `xmm15` and `xmm14` (`VConsts`), with the
zetas in Montgomery form in `xmm13` (`ZLanes`) and its odd doublewords in the
even ones of `xmm12` (`ZOdd`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly XKeep xmm_setXmm mxcsr_setXmm ifp ifn)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

/-- The doublewords of `x` are the values of the coefficients `f 0, …, f 3`. -/
def DLanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 4, (dword x i).toNat = (f i).val

/-- The doublewords of `x` are the zetas `ζ i · 2³² mod q` (Montgomery form). -/
def ZLanes (x : BitVec 128) (ζ : Nat → Zq) : Prop := ∀ i < 4, (dword x i).toNat = (ζ i).val * 2 ^ 32 % q

/-- The even doublewords of `zo` are the odd ones of `z`. -/
def ZOdd (z zo : BitVec 128) : Prop := ∀ j < 2, dword zo (2 * j) = dword z (2 * j + 1)

/-- The constants of the vector code are in place. -/
structure VConsts (s : State) : Prop where
  q : s.xmm .xmm15 = qV
  qinv : s.xmm .xmm14 = qinvV

theorem VConsts.setXmm {s : State} (hc : VConsts s) {d : XReg} (h14 : XReg.xmm14 ≠ d)
    (h15 : XReg.xmm15 ≠ d) (v : BitVec 128) : VConsts (s.setXmm d v) :=
  ⟨by rw [xmm_setXmm, ifn h15]; exact hc.q, by rw [xmm_setXmm, ifn h14]; exact hc.qinv⟩

theorem xonly_vconsts {rs : List XReg} {s s' : State} (h : XOnly rs s s') (hc : VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VConsts s' :=
  ⟨by rw [h.xmm _ h15, hc.q], by rw [h.xmm _ h14, hc.qinv]⟩

/-! ## Registers -/

/-- `vcadd` on a register. -/
def caddV (d : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd d (XBinOp.eval .pand (XShiftOp.eval .psrad d 31) qV)

/-- `vcsub` on a register. -/
def csubV (d : BitVec 128) : BitVec 128 := caddV (XBinOp.eval .psubd d qV)

theorem dword_psubd (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .psubd a b) i = dword a i - dword b i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XBinOp.eval]

theorem dword_pand (a b : BitVec 128) (i : Nat) :
    dword (XBinOp.eval .pand a b) i = dword a i &&& dword b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem dword_psrad (a : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrad a n) i = (dword a i).sshiftRight (min n.toNat 32) := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval]

theorem dword_caddV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (caddV d) i = caddL (dword d i) := by
  rw [caddV, dword_paddd _ _ hi, dword_pand, dword_psrad _ _ hi, dword_qV hi]; rfl

theorem dword_csubV (d : BitVec 128) {i : Nat} (hi : i < 4) : dword (csubV d) i = csubL (dword d i) := by
  rw [csubV, dword_caddV _ hi, dword_psubd _ _ hi, dword_qV hi]; rfl

/-- A reduced coefficient times a zeta in Montgomery form is less than `q · 2³²`. -/
theorem prod_lt {y z : BitVec 128} {f ζ : Nat → Zq} (hy : DLanes y f) (hz : ZLanes z ζ) :
    ∀ i < 4, (dword y i).toNat * (dword z i).toNat < q * 2 ^ 32 := fun i hi => by
  rw [hy i hi, hz i hi]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (f i)) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
    (by decide)) (by decide)

theorem subq_mul_lt {a b c : Nat} (ha : a < 8380417) (hb : b < 8380417) (hc : c < q) :
    (b + q - a) * c < q * 2 ^ 32 := by
  rw [q_eq] at *
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show b + 8380417 - a < 2 * 8380417 by omega)
    (Nat.le_of_lt hc) (by decide)) (by decide)

theorem eval_movdqa (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-! ## Butterflies -/

theorem vbfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : DLanes (s.xmm .xmm0) x)
    (hy : DLanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vbfly) s fun s' => DLanes (s'.xmm .xmm0) (fun i => x i + ζ i * y i) ∧
      DLanes (s'.xmm .xmm3) (fun i => x i - ζ i * y i) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vbfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (csubV (XBinOp.eval .paddd (s.xmm .xmm0)
      (csubV (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [dword_csubV _ hi, dword_paddd _ _ hi, dword_csubV _ hi]
    exact (bflyD (hx i hi) (mulZ (hy i hi) (hz i hi) (dword_montV ho (prod_lt hy hz) hi))).1
  · change DLanes (caddV (XBinOp.eval .psubd (s.xmm .xmm0)
      (csubV (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))))) _
    intro i hi
    rw [dword_caddV _ hi, dword_psubd _ _ hi, dword_csubV _ hi]
    exact (bflyD (hx i hi) (mulZ (hy i hi) (hz i hi) (dword_montV ho (prod_lt hy hz) hi))).2

theorem vibfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : DLanes (s.xmm .xmm0) x)
    (hy : DLanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12)) :
    WP isa (.block vibfly) s fun s' => DLanes (s'.xmm .xmm0) (fun i => x i + y i) ∧
      DLanes (s'.xmm .xmm3) (fun i => ζ i * (y i - x i)) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' := by
  simp only [vibfly, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  have e : ∀ i < 4, dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV) i =
      dword (s.xmm .xmm1) i - dword (s.xmm .xmm0) i + qB := fun i hi => by
    rw [dword_paddd _ _ hi, dword_psubd _ _ hi, dword_qV hi]
  have hb : ∀ i < 4, (dword (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV) i).toNat *
      (dword (s.xmm .xmm13) i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [e i hi, subq_toNat (by rw [hx i hi]; exact val_lt _) (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi,
      hz i hi]
    exact subq_mul_lt (val_lt (x i)) (val_lt (y i)) (Nat.mod_lt _ (by decide))
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (csubV (XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1))) _
    intro i hi
    rw [dword_csubV _ hi, dword_paddd _ _ hi, addD_toNat (by rw [hx i hi]; exact val_lt _)
      (by rw [hy i hi]; exact val_lt _), hx i hi, hy i hi, val_add]
  · change DLanes (csubV (montV (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0)) qV)
      (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    rw [dword_csubV _ hi]
    exact (ibflyD (hx i hi) (hy i hi) (hz i hi) (by rw [dword_montV ho hb hi, e i hi])).2

end VG.Proof.MlDsa.X86_64.Arith
