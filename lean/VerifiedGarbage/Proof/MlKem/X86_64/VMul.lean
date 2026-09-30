import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import Mathlib.Tactic.LinearCombination

/-!
# ML-KEM on x86-64: `BaseCaseMultiply` on words

Untrusted: everything here is checked by Lean. The words `vbase` computes
for a pair (`baseW`): with `mont(x, y) = x · y · 2⁻¹⁶ mod q`,
`mont(mont(a₀, b₀) + mont(mont(a₁, b₁), γ · 2¹⁶), R²)` is `a₀b₀ + a₁b₁γ` and
`mont(mont(a₀, b₁) + mont(a₁, b₀), R²)` is `a₀b₁ + a₁b₀`, modulo `q`.
-/

namespace VG.Proof.MlKem.X86_64.W

open VG VG.X86_64 VG.Proof.MlKem
open VG.Spec.MlKem (Zq)

/-- `R² mod q`, in a word. -/
def r2W : BitVec 16 := 1353#16

/-- `montW d z` for `d ∈ (-2q, 2q)` and `z ∈ (-q, q)`. -/
theorem mont_small {d z : BitVec 16} (hd1 : -(2 * 3329) < d.toInt) (hd2 : d.toInt < 2 * 3329)
    (hz1 : -3329 < z.toInt) (hz2 : z.toInt < 3329) :
    -3329 < (montW d z).toInt ∧ (montW d z).toInt < 3329 ∧
      3329 ∣ (montW d z).toInt * 65536 - d.toInt * z.toInt := by
  have hn : (d.toInt * z.toInt).natAbs ≤ 6657 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := Int.le_natAbs (a := d.toInt * z.toInt)
  have h2 := Int.le_natAbs (a := -(d.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := montW_spec (d := d) (z := z) (by omega) (by omega)
  exact ⟨m1, m2, Int.dvd_of_emod_eq_zero m3⟩

theorem toInt_lt_q {a : BitVec 16} {x : Zq} (h : a.toNat = x.val) : a.toInt = x.val ∧ 0 ≤ a.toInt ∧ a.toInt < 3329 := by
  have hx := x.isLt
  have e := toInt_of_lt (a := a) (by rw [h]; exact hx)
  rw [h] at e
  exact ⟨e, by rw [e]; exact Int.natCast_nonneg _, by rw [e]; exact Int.ofNat_lt.mpr hx⟩

/-- The value of a word in `[0, q)` from its value modulo `q`. -/
theorem cadd_val {m : BitVec 16} (h1 : -3329 < m.toInt) (h2 : m.toInt < 3329) {T : Int} {v : Zq}
    (hd : 3329 ∣ m.toInt - T) (hv : (v.val : Int) = T % 3329) : (caddW m).toNat = v.val := by
  have c := caddW_spec (Int.le_of_lt h1) h2
  have n := toNat_of_toInt (a := caddW m) (by rw [c]; exact Int.emod_nonneg _ (by decide))
  rw [c] at n
  obtain ⟨k, hk⟩ := hd
  omega

theorem mulmod (a b n : Nat) : a % n * b % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem r2W_toInt : r2W.toInt = 1353 := by decide

/-- The two words of `BaseCaseMultiply` (`vbase`), from the words `a₀, a₁,
b₀, b₁` and `γ · 2¹⁶ mod q`. -/
theorem baseW {a0 a1 b0 b1 g : BitVec 16} {x0 x1 y0 y1 γ : Zq} (ha0 : a0.toNat = x0.val)
    (ha1 : a1.toNat = x1.val) (hb0 : b0.toNat = y0.val) (hb1 : b1.toNat = y1.val)
    (hg : g.toNat = γ.val * 65536 % 3329) :
    (caddW (montW (montW a0 b0 + montW (montW a1 b1) g) r2W)).toNat = (x0 * y0 + x1 * y1 * γ).val ∧
      (caddW (montW (montW a0 b1 + montW a1 b0) r2W)).toNat = (x0 * y1 + x1 * y0).val := by
  obtain ⟨A0, A0l, A0h⟩ := toInt_lt_q ha0
  obtain ⟨A1, A1l, A1h⟩ := toInt_lt_q ha1
  obtain ⟨B0, B0l, B0h⟩ := toInt_lt_q hb0
  obtain ⟨B1, B1l, B1h⟩ := toInt_lt_q hb1
  have hgl : g.toNat < 3329 := by rw [hg]; exact Nat.mod_lt _ (by decide)
  have G := toInt_of_lt hgl
  rw [hg] at G
  have Gl : 0 ≤ g.toInt ∧ g.toInt < 3329 := by
    rw [G]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩
  have hγ := γ.isLt
  have kG : ∃ k : Int, g.toInt - (γ.val : Int) * 65536 = 3329 * k :=
    ⟨-((γ.val : Int) * 65536 / 3329), by rw [G]; push_cast; omega_using []⟩
  obtain ⟨kG, hkG⟩ := kG
  have r2l : -3329 < r2W.toInt ∧ r2W.toInt < 3329 := by rw [r2W_toInt]; decide
  -- the products
  obtain ⟨m1l, m1h, ⟨k1, d1⟩⟩ := mont_small (d := a1) (z := b1) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨m2l, m2h, ⟨k2, d2⟩⟩ := mont_small (d := montW a1 b1) (z := g) (by omega_using [m1l])
    (by omega_using [m1h]) (by omega_using [Gl]) (by omega_using [Gl])
  obtain ⟨m3l, m3h, ⟨k3, d3⟩⟩ := mont_small (d := a0) (z := b0) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B0l]) (by omega_using [B0h])
  obtain ⟨n1l, n1h, ⟨j1, e1⟩⟩ := mont_small (d := a0) (z := b1) (by omega_using [A0l]) (by omega_using [A0h])
    (by omega_using [B1l]) (by omega_using [B1h])
  obtain ⟨n2l, n2h, ⟨j2, e2⟩⟩ := mont_small (d := a1) (z := b0) (by omega_using [A1l]) (by omega_using [A1h])
    (by omega_using [B0l]) (by omega_using [B0h])
  have S1 := toInt_add16 (a := montW a0 b0) (b := montW (montW a1 b1) g) (by omega_using [m3l, m2l])
    (by omega_using [m3h, m2h])
  have S2 := toInt_add16 (a := montW a0 b1) (b := montW a1 b0) (by omega_using [n1l, n2l])
    (by omega_using [n1h, n2h])
  obtain ⟨m4l, m4h, ⟨k4, d4⟩⟩ := mont_small (d := montW a0 b0 + montW (montW a1 b1) g) (z := r2W)
    (by rw [S1]; omega_using [m3l, m2l]) (by rw [S1]; omega_using [m3h, m2h]) r2l.1 r2l.2
  obtain ⟨n4l, n4h, ⟨j4, e4⟩⟩ := mont_small (d := montW a0 b1 + montW a1 b0) (z := r2W)
    (by rw [S2]; omega_using [n1l, n2l]) (by rw [S2]; omega_using [n1h, n2h]) r2l.1 r2l.2
  rw [S1, r2W_toInt] at d4
  rw [S2, r2W_toInt] at e4
  simp only [A0, A1, B0, B1] at d1 d3 e1 e2
  refine ⟨cadd_val m4l m4h (T := ((x0.val * y0.val + x1.val * y1.val * γ.val : Nat) : Int)) ?_ ?_,
    cadd_val n4l n4h (T := ((x0.val * y1.val + x1.val * y0.val : Nat) : Int)) ?_ ?_⟩
  · generalize (montW (montW a0 b0 + montW (montW a1 b1) g) r2W).toInt = M4 at *
    generalize (montW (montW a1 b1) g).toInt = M2 at *
    generalize (montW a0 b0).toInt = M3 at *
    generalize (montW a1 b1).toInt = M1 at *
    generalize g.toInt = Gi at *
    refine ⟨-3327 * M4 + 169 * k4 + 49 * (M3 + M2) + k3 + k2 + M1 * kG + γ.val * k1, ?_⟩
    push_cast
    linear_combination 169 * d4 + d3 + d2 + M1 * hkG + (γ.val : Int) * d1
  · rw [val_add', val_mul, val_mul, val_mul, mulmod, ← Nat.add_mod]; push_cast; rfl
  · generalize (montW (montW a0 b1 + montW a1 b0) r2W).toInt = M4 at *
    generalize (montW a0 b1).toInt = N1 at *
    generalize (montW a1 b0).toInt = N2 at *
    refine ⟨-3327 * M4 + 169 * j4 + 49 * (N1 + N2) + j1 + j2, ?_⟩
    push_cast
    linear_combination 169 * e4 + e1 + e2
  · rw [val_add', val_mul, val_mul, ← Nat.add_mod]; push_cast; rfl

end VG.Proof.MlKem.X86_64.W

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `R² mod q` in every word. -/
def r2V : BitVec 128 := 0x05490549054905490549054905490549#128

theorem word_r2V {i : Nat} (hi : i < 8) : word r2V i = W.r2W := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `d ← mont(src, z)`. -/
theorem movmont_ok {d src z t : XReg} (h1 : z ≠ d) (h2 : t ≠ d) (h3 : z ≠ t) (h5 : XReg.xmm15 ≠ d)
    (h6 : XReg.xmm14 ≠ t) (h7 : XReg.xmm15 ≠ t) (h8 : XReg.xmm14 ≠ d) {s : State} (hc : VConsts s) :
    WP isa (.block (xmov d src :: vmont d z t)) s fun s' =>
      WLanes (s'.xmm d) (fun i => W.montW (word (s.xmm src) i) (word (s.xmm z) i)) ∧ XOnly [d, t] s s' := by
  rw [show xmov d src :: vmont d z t = [xmov d src] ++ vmont d z t from rfl, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  refine WP.mono (vmont_ok h2 h3 h5 h6 h7 (hc.setXmm h8 h5 _)) fun s' ⟨l, o⟩ => ⟨fun i hi => ?_, ?_⟩
  · rw [l i hi, xmm_setXmm, xmm_setXmm, ifp rfl, ifn h1]; dsimp only; rw [word_movdqa]
  · exact ((XOnly.setXmm (by simp) (XOnly.refl [d] s) _).trans o).mono (by simp)

/-- `d ← d + e`, on words. -/
theorem paddw_ok {d e : XReg} {s : State} :
    WP isa (.block [xb .paddw d e]) s fun s' =>
      (∀ i < 8, word (s'.xmm d) i = word (s.xmm d) i + word (s.xmm e) i) ∧ XOnly [d] s s' := by
  simp only [xb]
  vrun
  exact ⟨fun i hi => word_paddw (a := s.xmm d) (b := s.xmm e) hi, by xonly⟩

theorem block_cons_iff {i : Instr} {l : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: l)) s Q ↔ WP isa (.block [i]) s fun s1 => WP isa (.block l) s1 Q := by
  rw [← WP.block_append_iff]; rfl

/-- `vbase`: `BaseCaseMultiply` on the eight pairs of lanes. -/
theorem vbase_ok {s : State} (hc : VConsts s) (hr : s.xmm .xmm12 = r2V) {x0 x1 y0 y1 γ : Nat → Zq}
    (h0 : Lanes (s.xmm .xmm0) x0) (h4 : Lanes (s.xmm .xmm4) x1) (h6 : Lanes (s.xmm .xmm6) y0)
    (h10 : Lanes (s.xmm .xmm10) y1) (h13 : ZLanes (s.xmm .xmm13) γ) :
    WP isa (.block vbase) s fun s' => Lanes (s'.xmm .xmm1) (fun i => x0 i * y0 i + x1 i * y1 i * γ i) ∧
      Lanes (s'.xmm .xmm2) (fun i => x0 i * y1 i + x1 i * y0 i) ∧
      XOnly [.xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  simp only [vbase, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm1) (src := .xmm4) (z := .xmm10) (t := .xmm2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  have c2 := o2.consts c1 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm6) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c2) fun s3 ⟨l3, o3⟩ => ?_
  have c3 := o3.consts c2 (by decide) (by decide)
  rw [WP.block_append_iff, block_cons_iff]
  refine WP.mono (paddw_ok (d := .xmm1) (e := .xmm2)) fun s4 ⟨l4, o4⟩ => ?_
  have c4 := o4.consts c3 (by decide) (by decide)
  refine WP.mono (movmont_ok (d := .xmm2) (src := .xmm0) (z := .xmm10) (t := .xmm3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) c4) fun s5 ⟨l5, o5⟩ => ?_
  have c5 := o5.consts c4 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm4) (z := .xmm6) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c5) fun s6 ⟨l6, o6⟩ => ?_
  have c6 := o6.consts c5 (by decide) (by decide)
  rw [WP.block_append_iff, block_cons_iff]
  refine WP.mono (paddw_ok (d := .xmm2) (e := .xmm4)) fun s7 ⟨l7, o7⟩ => ?_
  have c7 := o7.consts c6 (by decide) (by decide)
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm12) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c7) fun s8 ⟨l8, o8⟩ => ?_
  have c8 := o8.consts c7 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vcadd_ok (d := .xmm1) (t := .xmm3) (by decide) (by decide) c8) fun s9 ⟨l9, o9⟩ => ?_
  have c9 := o9.consts c8 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm2) (z := .xmm12) (t := .xmm3) (by decide) (by decide) (by decide)
    (by decide) (by decide) c9) fun s10 ⟨l10, o10⟩ => ?_
  have c10 := o10.consts c9 (by decide) (by decide)
  refine WP.mono (vcadd_ok (d := .xmm2) (t := .xmm3) (by decide) (by decide) c10) fun s11 ⟨l11, o11⟩ => ?_
  -- the registers each step reads
  have e0 : s4.xmm .xmm0 = s.xmm .xmm0 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e6 : s5.xmm .xmm6 = s.xmm .xmm6 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have e10 : s4.xmm .xmm10 = s.xmm .xmm10 := by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]
  have e12 : ∀ t, t = s7 ∨ t = s9 → t.xmm .xmm12 = r2V := by
    rintro t (rfl | rfl)
    · rw [o7.xmm _ (by decide), o6.xmm _ (by decide), o5.xmm _ (by decide), o4.xmm _ (by decide),
        o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide), hr]
    · rw [o9.xmm _ (by decide), o8.xmm _ (by decide), o7.xmm _ (by decide), o6.xmm _ (by decide),
        o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
        o1.xmm _ (by decide), hr]
  have e4 : s5.xmm .xmm4 = s.xmm .xmm4 := by
    rw [o5.xmm _ (by decide), o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide),
      o1.xmm _ (by decide)]
  have v1 : ∀ i < 8, word (s9.xmm .xmm1) i = W.caddW (W.montW (W.montW (word (s.xmm .xmm0) i)
      (word (s.xmm .xmm6) i) + W.montW (W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm10) i))
        (word (s.xmm .xmm13) i)) W.r2W) := fun i hi => by
    rw [l9 i hi]; dsimp only; rw [l8 i hi]; dsimp only
    rw [e12 s7 (.inl rfl), word_r2V hi, o7.xmm _ (by decide), o6.xmm _ (by decide), o5.xmm _ (by decide),
      l4 i hi, o3.xmm _ (by decide), l2 i hi, l3 i hi]
    dsimp only
    rw [l1 i hi, o1.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide), BitVec.add_comm]
    dsimp only
    rw [o2.xmm .xmm6 (by decide), o1.xmm .xmm6 (by decide)]
  have v2 : ∀ i < 8, word (s11.xmm .xmm2) i = W.caddW (W.montW (W.montW (word (s.xmm .xmm0) i)
      (word (s.xmm .xmm10) i) + W.montW (word (s.xmm .xmm4) i) (word (s.xmm .xmm6) i)) W.r2W) :=
    fun i hi => by
      rw [l11 i hi]; dsimp only; rw [l10 i hi]; dsimp only
      rw [e12 s9 (.inr rfl), word_r2V hi, o9.xmm _ (by decide), o8.xmm _ (by decide), l7 i hi,
        o6.xmm _ (by decide), l6 i hi, l5 i hi]
      dsimp only
      rw [e0, e10, e4, e6]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [o11.xmm _ (by decide), o10.xmm _ (by decide), v1 i hi]
    exact (W.baseW (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).1
  · rw [v2 i hi]
    exact (W.baseW (h0 i hi) (h4 i hi) (h6 i hi) (h10 i hi) (h13 i hi)).2
  · refine ((o1.trans (o2.trans (o3.trans (o4.trans (o5.trans (o6.trans (o7.trans (o8.trans
      (o9.trans (o10.trans o11)))))))))).mono ?_)
    simp

/-! ## Loads and stores -/

/-- The words `deint` leaves of the even doublewords of `l0, …, l3`. -/
def deE (l0 l1 l2 l3 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XBinOp.eval .punpcklqdq (shufDwords l0 0xD8) (shufDwords l1 0xD8))
    (XBinOp.eval .punpcklqdq (shufDwords l2 0xD8) (shufDwords l3 0xD8))

/-- The words `deint` leaves of the odd doublewords of `l0, …, l3`. -/
def deO (l0 l1 l2 l3 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XBinOp.eval .punpckhqdq (shufDwords l0 0xD8) (shufDwords l1 0xD8))
    (XBinOp.eval .punpckhqdq (shufDwords l2 0xD8) (shufDwords l3 0xD8))

theorem shuf_d8 (a : BitVec 128) : shufDwords a 0xD8 = ofDwords (dword a 0) (dword a 2) (dword a 1) (dword a 3) := by
  apply ext_dword <;> simp [dword_shufDwords]

theorem deint_lanes {l0 l1 l2 l3 : BitVec 128} {c : Nat → Nat}
    (h0 : ∀ j < 4, (dword l0 j).toNat = c j) (h1 : ∀ j < 4, (dword l1 j).toNat = c (4 + j))
    (h2 : ∀ j < 4, (dword l2 j).toNat = c (8 + j)) (h3 : ∀ j < 4, (dword l3 j).toNat = c (12 + j))
    (hs : ∀ k < 16, c k < 32768) :
    (∀ e < 8, (word (deE l0 l1 l2 l3) e).toNat = c (2 * e)) ∧
      (∀ e < 8, (word (deO l0 l1 l2 l3) e).toNat = c (2 * e + 1)) := by
  have lo : ∀ a b : BitVec 128, XBinOp.eval .punpcklqdq (shufDwords a 0xD8) (shufDwords b 0xD8) =
      ofDwords (dword a 0) (dword a 2) (dword b 0) (dword b 2) := fun a b => by
    rw [punpcklqdq_eq, shuf_d8, shuf_d8]; simp
  have hi : ∀ a b : BitVec 128, XBinOp.eval .punpckhqdq (shufDwords a 0xD8) (shufDwords b 0xD8) =
      ofDwords (dword a 1) (dword a 3) (dword b 1) (dword b 3) := fun a b => by
    rw [punpckhqdq_eq, shuf_d8, shuf_d8]; simp
  have sm : ∀ a b c d : BitVec 32, a.toNat < 32768 → b.toNat < 32768 → c.toNat < 32768 → d.toNat < 32768 →
      ∀ j < 4, (dword (ofDwords a b c d) j).toNat < 32768 := fun a b c d ha hb hc hd j hj => by
    rcases cases4 hj with rfl | rfl | rfl | rfl <;> simpa
  have t0 : ∀ j < 4, (dword l0 j).toNat < 32768 := fun j hj => by rw [h0 j hj]; exact hs j (by omega)
  have t1 : ∀ j < 4, (dword l1 j).toNat < 32768 := fun j hj => by rw [h1 j hj]; exact hs _ (by omega)
  have t2 : ∀ j < 4, (dword l2 j).toNat < 32768 := fun j hj => by rw [h2 j hj]; exact hs _ (by omega)
  have t3 : ∀ j < 4, (dword l3 j).toNat < 32768 := fun j hj => by rw [h3 j hj]; exact hs _ (by omega)
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [deE, lo, lo, word_packssdw_small _ _ he (sm _ _ _ _ (t0 0 (by decide)) (t0 2 (by decide))
      (t1 0 (by decide)) (t1 2 (by decide))) (sm _ _ _ _ (t2 0 (by decide)) (t2 2 (by decide))
      (t3 0 (by decide)) (t3 2 (by decide)))]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, dword_ofDwords_0, dword_ofDwords_1,
        dword_ofDwords_2, dword_ofDwords_3, h0 _ (by decide : 0 < 4), h0 _ (by decide : 2 < 4),
        h1 _ (by decide : 0 < 4), h1 _ (by decide : 2 < 4), h2 _ (by decide : 0 < 4), h2 _ (by decide : 2 < 4),
        h3 _ (by decide : 0 < 4), h3 _ (by decide : 2 < 4)]
  · rw [deO, hi, hi, word_packssdw_small _ _ he (sm _ _ _ _ (t0 1 (by decide)) (t0 3 (by decide))
      (t1 1 (by decide)) (t1 3 (by decide))) (sm _ _ _ _ (t2 1 (by decide)) (t2 3 (by decide))
      (t3 1 (by decide)) (t3 3 (by decide)))]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub, dword_ofDwords_0, dword_ofDwords_1,
        dword_ofDwords_2, dword_ofDwords_3, h0 _ (by decide : 1 < 4), h0 _ (by decide : 3 < 4),
        h1 _ (by decide : 1 < 4), h1 _ (by decide : 3 < 4), h2 _ (by decide : 1 < 4), h2 _ (by decide : 3 < 4),
        h3 _ (by decide : 1 < 4), h3 _ (by decide : 3 < 4)]
theorem deintF_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 32) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 48) 16) :
    WP isa (.block (deint .rsi .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) s fun s' =>
      s'.xmm .xmm0 = deE (s.mem.readW (s.gpr .rsi) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 48) 128) ∧
      s'.xmm .xmm4 = deO (s.mem.readW (s.gpr .rsi) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 48) 128) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s' := by
  simp only [deint]
  vrunm [h0, h1, h2, h3, eval_movdqa]
  exact ⟨rfl, rfl, by xonly⟩
theorem deintG_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 48) 16) :
    WP isa (.block (deint .rdx .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) s fun s' =>
      s'.xmm .xmm6 = deE (s.mem.readW (s.gpr .rdx) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 48) 128) ∧
      s'.xmm .xmm10 = deO (s.mem.readW (s.gpr .rdx) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 16) 128)
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 32) 128) (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 48) 128) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  simp only [deint]
  vrunm [h0, h1, h2, h3, eval_movdqa]
  exact ⟨rfl, rfl, by xonly⟩

theorem off16 (H : Addr) (j t : Nat) : coeffAddr H j + BitVec.ofNat 64 (16 * t) = coeffAddr H (j + 4 * t) := by
  rw [show 16 * t = 4 * (4 * t) by omega, coeffAddr_off]

/-- Four stores of 16 bytes to coefficients `j, …, j + 15` of the polynomial at `H`. -/
theorem store4 (m : Mem) (H : Addr) {j : Nat} (hj : j + 16 ≤ 256) (Y0 Y1 Y2 Y3 : BitVec 128) :
    let m' := (((m.writeW (coeffAddr H j) Y0).writeW (coeffAddr H j + BitVec.ofNat 64 16) Y1).writeW
      (coeffAddr H j + BitVec.ofNat 64 32) Y2).writeW (coeffAddr H j + BitVec.ofNat 64 48) Y3
    (∀ k < 256, k < j ∨ j + 16 ≤ k → coeffAt m' H k = coeffAt m H k) ∧
      (∀ k < 16, coeffAt m' H (j + k) = dword ([Y0, Y1, Y2, Y3][k / 4]!) (k % 4)) ∧
      Frame [pR H] m m' := by
  intro m'
  have a1 := off16 H j 1
  have a2 := off16 H j 2
  have a3 := off16 H j 3
  simp only [Nat.mul_one] at a1
  simp only [show 16 * 2 = 32 from rfl, show 16 * 3 = 48 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl] at a2 a3
  simp only [m', a1, a2, a3]
  refine ⟨fun k hk ho => ?_, fun k hk => ?_, ?_⟩
  · rw [coeffAt_write128 _ _ (by omega) _ hk, coeffAt_write128 _ _ (by omega) _ hk,
      coeffAt_write128 _ _ (by omega) _ hk, coeffAt_write128 _ _ (by omega) _ hk]
    simp (disch := omega) only [ite_eq_right]
  · rw [coeffAt_write128 _ _ (by omega) _ (by omega), coeffAt_write128 _ _ (by omega) _ (by omega),
      coeffAt_write128 _ _ (by omega) _ (by omega), coeffAt_write128 _ _ (by omega) _ (by omega)]
    rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 16)) with h | h | h | h
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - j = k % 4 by omega, show k / 4 = 0 by omega]; rfl
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - (j + 4) = k % 4 by omega, show k / 4 = 1 by omega]; rfl
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      rw [show j + k - (j + 8) = k % 4 by omega, show k / 4 = 2 by omega]; rfl
    · simp (disch := omega) only [ite_eq_left]
      rw [show j + k - (j + 12) = k % 4 by omega, show k / 4 = 3 by omega]; rfl
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The words `vinter` interleaves, as the `u32` it stores for each. -/
theorem inter_val (X1 X2 : BitVec 128) {k : Nat} (hk : k < 16) :
    (dword ([XBinOp.eval .punpcklwd (XBinOp.eval .punpcklwd X1 X2) 0,
      XBinOp.eval .punpckhwd (XBinOp.eval .punpcklwd X1 X2) 0,
      XBinOp.eval .punpcklwd (XBinOp.eval .punpckhwd X1 X2) 0,
      XBinOp.eval .punpckhwd (XBinOp.eval .punpckhwd X1 X2) 0][k / 4]!) (k % 4)).toNat =
      (word (if k % 2 = 0 then X1 else X2) (k / 2)).toNat := by
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ (12 ≤ k ∧ k < 16)) with h | h | h | h
  · rw [show k / 4 = 0 by omega]
    simp only [List.getElem!_cons_zero]
    rw [dword_punpcklwd0 _ (by omega), word_punpcklwd _ _ (by omega), show k % 4 / 2 = k / 2 by omega,
      show k % 4 % 2 = k % 2 by omega]
    split <;> rfl
  · rw [show k / 4 = 1 by omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpckhwd0 _ (by omega), word_punpcklwd _ _ (by omega), show (4 + k % 4) / 2 = k / 2 by omega,
      show (4 + k % 4) % 2 = k % 2 by omega]
    split <;> rfl
  · rw [show k / 4 = 2 by omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpcklwd0 _ (by omega), word_punpckhwd _ _ (by omega), show 4 + k % 4 / 2 = k / 2 by omega,
      show k % 4 % 2 = k % 2 by omega]
    split <;> rfl
  · rw [show k / 4 = 3 by omega]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [dword_punpckhwd0 _ (by omega), word_punpckhwd _ _ (by omega),
      show 4 + (4 + k % 4) / 2 = k / 2 by omega, show (4 + k % 4) % 2 = k % 2 by omega]
    split <;> rfl

theorem vinter_ok {s : State} {H : Addr} {j : Nat} (hj : j + 16 ≤ 256) (hdi : s.gpr .rdi = coeffAddr H j)
    (hw : pR H ∈ s.wr) :
    WP isa (.block vinter) s fun s' =>
      (∀ k < 256, k < j ∨ j + 16 ≤ k → coeffAt s'.mem H k = coeffAt s.mem H k) ∧
      (∀ k < 16, (coeffAt s'.mem H (j + k)).toNat =
        (word (if k % 2 = 0 then s.xmm .xmm1 else s.xmm .xmm2) (k / 2)).toNat) ∧
      Frame [pR H] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧
      ∀ r, r ∉ [XReg.xmm1, .xmm3, .xmm4, .xmm5, .xmm6] → s'.xmm r = s.xmm r := by
  have w : ∀ t < 4, InRegions s.wr (coeffAddr H j + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [off16]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
  have w0 : InRegions s.wr (coeffAddr H j) 16 := by
    have := w 0 (by decide); rwa [Nat.mul_zero, add_ofNat_zero] at this
  simp only [vinter]
  vrunm [hdi, eval_movdqa, pxor_self, w0, w 1 (by decide), w 2 (by decide), w 3 (by decide)]
  obtain ⟨o, v, f⟩ := store4 s.mem H hj
    (XBinOp.eval .punpcklwd (XBinOp.eval .punpcklwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpckhwd (XBinOp.eval .punpcklwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpcklwd (XBinOp.eval .punpckhwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
    (XBinOp.eval .punpckhwd (XBinOp.eval .punpckhwd (s.xmm .xmm1) (s.xmm .xmm2)) 0)
  refine ⟨o, fun k hk => by rw [v k hk]; exact inter_val _ _ hk, f, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
end VG.Proof.MlKem.X86_64
