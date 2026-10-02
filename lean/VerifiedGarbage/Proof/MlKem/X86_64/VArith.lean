import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM on x86-64: arithmetic modulo `q` in 16-bit words

What `vmont`, `vcadd` and `vcsub` (`Impl/MlKem/X86_64/Vec.lean`) compute in
each word (`montW`, `caddW`, `csubW`), on the words' signed values
(`BitVec.toInt`):

* `montW_spec`: `montW d z` is in `(-q, q)` and congruent to
  `d · z · 2⁻¹⁶` modulo `q`, if `|d · z| < q · 2¹⁵`;
* `caddW_spec`, `csubW_spec`: the value modulo `q`, in `[0, q)`, of a word in
  `(-q, q)` or `[0, 2q)`.
-/

namespace VG.Proof.MlKem.X86_64.W

open VG VG.X86_64 VG.Proof.MlKem

/-- `q` as a word. -/
def qW : BitVec 16 := 3329

/-- `q⁻¹ mod 2¹⁶` as a word. -/
def qinvW : BitVec 16 := 62209

/-- The word `vmont` leaves of the words `d` and `z`. -/
def montW (d z : BitVec 16) : BitVec 16 :=
  (mulWordsSigned d z).extractLsb' 16 16 -
    (mulWordsSigned ((mulWordsSigned ((mulWordsSigned d z).extractLsb' 0 16) qinvW).extractLsb' 0 16)
      qW).extractLsb' 16 16

/-- The word `vcadd` leaves of `d`. -/
def caddW (d : BitVec 16) : BitVec 16 := d + ((d.sshiftRight (min 15 16)) &&& qW)

/-- The word `vcsub` leaves of `d`. -/
def csubW (d : BitVec 16) : BitVec 16 := caddW (d - qW)

/-! ## Words as integers -/

theorem toInt16 (x : BitVec 16) :
    x.toInt = if x.toNat < 32768 then (x.toNat : Int) else (x.toNat : Int) - 65536 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega

theorem toInt32 (x : BitVec 32) :
    x.toInt = if x.toNat < 2147483648 then (x.toNat : Int) else (x.toNat : Int) - 4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega

theorem toInt16_bounds (x : BitVec 16) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  rw [toInt16]; have := x.isLt; split <;> omega

/-- A word is determined by its value modulo `2¹⁶` and its range. -/
theorem toInt16_eq {x : BitVec 16} {v : Int} (h1 : -32768 ≤ v) (h2 : v < 32768)
    (h : ((x.toNat : Int) - v) % 65536 = 0) : x.toInt = v := by
  rw [toInt16]; have := x.isLt; split <;> omega

theorem toNat16_eq {x : BitVec 16} : (x.toNat : Int) % 65536 = x.toInt % 65536 := by
  rw [toInt16]; have := x.isLt; split <;> omega

/-- The product of two words is at most `2³⁰` in magnitude. -/
theorem mul_bounds (a b : BitVec 16) : -(2 ^ 30 : Int) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 2 ^ 30 := by
  have ha := toInt16_bounds a
  have hb := toInt16_bounds b
  have hn : (a.toInt * b.toInt).natAbs ≤ 32768 * 32768 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := Int.le_natAbs (a := a.toInt * b.toInt)
  have h2 := Int.le_natAbs (a := -(a.toInt * b.toInt))
  rw [Int.natAbs_neg] at h2
  omega

theorem toInt_mulWordsSigned (a b : BitVec 16) : (mulWordsSigned a b).toInt = a.toInt * b.toInt := by
  rw [mulWordsSigned, BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by decide),
    BitVec.toInt_signExtend_of_le (by decide)]
  have := mul_bounds a b
  apply Int.bmod_eq_of_le
  · rw [show (((2 ^ 32 : Nat) : Int) / 2) = 2147483648 from rfl]; omega
  · rw [show ((((2 ^ 32 : Nat) : Int) + 1) / 2) = 2147483648 from rfl]; omega

/-- The high word of a doubleword: its value divided by `2¹⁶`, rounded down. -/
theorem toInt_hi (x : BitVec 32) : (x.extractLsb' 16 16).toInt = x.toInt / 65536 := by
  rw [toInt16, toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega

/-- The low word of a doubleword: its value modulo `2¹⁶`. -/
theorem toInt_lo (x : BitVec 32) : ((x.extractLsb' 0 16).toInt - x.toInt) % 65536 = 0 := by
  rw [toInt16, toInt32, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have := x.isLt
  simp only [Nat.reducePow]
  split <;> split <;> omega

theorem toInt_sub16 {a b : BitVec 16} (h1 : -32768 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 32768) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

theorem toInt_add16 {a b : BitVec 16} (h1 : -32768 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 32768) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]; exact Int.bmod_eq_of_le (by simpa using h1) (by simpa using h2)

theorem qW_toInt : qW.toInt = 3329 := by decide
theorem qinvW_toInt : qinvW.toInt = -3327 := by decide

/-! ## Montgomery reduction -/

/-- `montW d z` is in `(-q, q)` and `2¹⁶ · montW d z ≡ d · z (mod q)`. -/
theorem montW_spec {d z : BitVec 16} (h1 : -(3329 * 32768) < d.toInt * z.toInt)
    (h2 : d.toInt * z.toInt < 3329 * 32768) :
    -3329 < (montW d z).toInt ∧ (montW d z).toInt < 3329 ∧
      ((montW d z).toInt * 65536 - d.toInt * z.toInt) % 3329 = 0 := by
  generalize hP : d.toInt * z.toInt = P at h1 h2
  have eP : (mulWordsSigned d z).toInt = P := by rw [toInt_mulWordsSigned, hP]
  generalize hL : (mulWordsSigned d z).extractLsb' 0 16 = L
  have hL' := toInt_lo (mulWordsSigned d z)
  rw [hL, eP] at hL'
  have bL := toInt16_bounds L
  generalize hT : (mulWordsSigned L qinvW).extractLsb' 0 16 = T
  have hT' := toInt_lo (mulWordsSigned L qinvW)
  rw [hT, toInt_mulWordsSigned, qinvW_toInt] at hT'
  have bT := toInt16_bounds T
  have hH := toInt_hi (mulWordsSigned d z)
  rw [eP] at hH
  have hM := toInt_hi (mulWordsSigned T qW)
  rw [toInt_mulWordsSigned, qW_toInt] at hM
  have e : montW d z = (mulWordsSigned d z).extractLsb' 16 16 - (mulWordsSigned T qW).extractLsb' 16 16 := by
    rw [montW, hL, hT]
  have hc : (P - T.toInt * 3329) % 65536 = 0 := by omega
  have hd : P / 65536 - T.toInt * 3329 / 65536 = (P - T.toInt * 3329) / 65536 := by omega
  rw [e, toInt_sub16 (by omega) (by omega), hH, hM, hd]
  omega

/-! ## Conditional additions of `q` -/

theorem sshiftRight15 (d : BitVec 16) :
    d.sshiftRight (min 15 16) = if d.toInt < 0 then -1 else 0 := by
  rw [show min 15 16 = 15 from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight]
  have := toInt16_bounds d
  split
  · rw [show (-1 : BitVec 16).toInt = -1 by decide, Int.shiftRight_eq_div_pow]; omega
  · rw [show (0 : BitVec 16).toInt = 0 by decide, Int.shiftRight_eq_div_pow]; omega

/-- `caddW d` is the value of `d ∈ [-q, q)` modulo `q`. -/
theorem caddW_spec {d : BitVec 16} (h1 : -3329 ≤ d.toInt) (h2 : d.toInt < 3329) :
    (caddW d).toInt = d.toInt % 3329 := by
  rw [caddW, sshiftRight15]
  split
  · rw [show (-1 : BitVec 16) &&& qW = qW by decide, toInt_add16 (by rw [qW_toInt]; omega)
      (by rw [qW_toInt]; omega), qW_toInt]
    omega
  · rw [show d + ((0 : BitVec 16) &&& qW) = d by rw [show (0 : BitVec 16) &&& qW = 0 by decide]; simp]
    omega

/-- `csubW d` is the value of `d ∈ [0, 2q)` modulo `q`. -/
theorem csubW_spec {d : BitVec 16} (h1 : 0 ≤ d.toInt) (h2 : d.toInt < 2 * 3329) :
    (csubW d).toInt = d.toInt % 3329 := by
  have e := toInt_sub16 (a := d) (b := qW) (by rw [qW_toInt]; omega) (by rw [qW_toInt]; omega)
  rw [qW_toInt] at e
  rw [csubW, caddW_spec (d := d - qW) (by rw [e]; omega) (by rw [e]; omega), e]
  omega

/-! ## Coefficients -/

open VG.Spec.MlKem (Zq)

theorem toInt_of_lt {a : BitVec 16} (h : a.toNat < 3329) : a.toInt = a.toNat := by
  rw [toInt16, ite_eq_left_of_eq_true _ _ (by simp; omega)]

theorem toNat_of_toInt {a : BitVec 16} (h : 0 ≤ a.toInt) : (a.toNat : Int) = a.toInt := by
  rw [toInt16] at h ⊢; have := a.isLt; split at h <;> [rw [ite_eq_left_of_eq_true _ _ (by simp; omega)]; omega]

/-- Cancelling `2¹⁶` modulo `q`: `2¹⁶ · 169 ≡ 1 (mod q)`. -/
theorem cancel_R {r P Y : Int} (h1 : (r * 65536 - P) % 3329 = 0) (h2 : (P - Y * 65536) % 3329 = 0) :
    r % 3329 = Y % 3329 := by
  omega

/-- `b · (ζ · 2¹⁶ mod q) ≡ y · ζ · 2¹⁶ (mod q)` for `b ≡ y (mod q)`. -/
theorem mul_zm {b y ζ z : Int} (hby : (b - y) % 3329 = 0) (hz : z = ζ * 65536 % 3329) :
    (b * z - y * ζ * 65536) % 3329 = 0 := by
  have e : b * z - y * ζ * 65536 = (b - y) * z + y * (z - ζ * 65536) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_assoc y ζ]; omega
  rw [e]
  apply Int.emod_eq_zero_of_dvd
  refine Int.dvd_add (Int.dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hby))
    (Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero ?_))
  rw [hz]; omega

/-- `ζ · y mod q`, from a word `b ≡ y (mod q)` in `(-q, q)` and the word
`ζ · 2¹⁶ mod q`. -/
theorem mulZ_spec {b z : BitVec 16} {y ζ : Zq} (hb1 : -3329 < b.toInt) (hb2 : b.toInt < 3329)
    (hby : (b.toInt - (y.val : Int)) % 3329 = 0) (hz : z.toNat = ζ.val * 65536 % 3329) :
    (caddW (montW b z)).toInt = (ζ * y).val := by
  have hzl : z.toNat < 3329 := by rw [hz]; exact Nat.mod_lt _ (by decide)
  have hzi := toInt_of_lt hzl
  have hn : (b.toInt * z.toInt).natAbs ≤ 3328 * 3328 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have h1 := Int.le_natAbs (a := b.toInt * z.toInt)
  have h2 := Int.le_natAbs (a := -(b.toInt * z.toInt))
  rw [Int.natAbs_neg] at h2
  obtain ⟨m1, m2, m3⟩ := montW_spec (d := b) (z := z) (by omega) (by omega)
  have hzI : z.toInt = (ζ.val : Int) * 65536 % 3329 := by rw [hzi]; omega
  have hm := mul_zm (ζ := (ζ.val : Int)) hby hzI
  rw [caddW_spec (Int.le_of_lt m1) m2, val_mul, cancel_R m3 hm, Int.natCast_emod, Int.natCast_mul,
    Int.mul_comm (ζ.val : Int)]
  rfl

/-- The value modulo `q` of a sum or a difference of two words less than `q`. -/
theorem addsub_int {A T : Int} (hA : 0 ≤ A ∧ A < 3329) (hT : 0 ≤ T ∧ T < 3329) :
    (-32768 ≤ A + T ∧ A + T < 32768 ∧ 0 ≤ A + T ∧ A + T < 2 * 3329) ∧
      (-32768 ≤ A - T ∧ A - T < 32768 ∧ -3329 ≤ A - T ∧ A - T < 3329) := by
  omega

/-- The two words of a butterfly of Algorithm 9 (`vbfly`): `x + ζ y` and
`x - ζ y`, from the words `x`, `y` and `ζ · 2¹⁶ mod q`. -/
theorem bflyW {a b z : BitVec 16} {x y ζ : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 65536 % 3329) :
    (csubW (a + caddW (montW b z))).toNat = (x + ζ * y).val ∧
      (caddW (a - caddW (montW b z))).toNat = (x - ζ * y).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have ht := mulZ_spec (b := b) (y := y) (ζ := ζ) (by rw [bi]; omega) (by rw [bi]; omega)
    (by rw [bi, Int.sub_self]; rfl) hz
  have hzy := val_lt (ζ * y)
  generalize caddW (montW b z) = t at ht
  obtain ⟨⟨p1, p2, p3, p4⟩, ⟨m1, m2, m3, m4⟩⟩ :=
    addsub_int (A := a.toInt) (T := t.toInt) (by rw [ai]; omega)
      (by rw [ht]; exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hzy⟩)
  rw [← toInt_add16 p1 p2] at p3 p4
  rw [← toInt_sub16 m1 m2] at m3 m4
  have c1 := csubW_spec p3 p4
  have c2 := caddW_spec m3 m4
  rw [toInt_add16 p1 p2] at c1
  rw [toInt_sub16 m1 m2] at c2
  have n1 := toNat_of_toInt (a := csubW (a + t)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  have n2 := toNat_of_toInt (a := caddW (a - t)) (by rw [c2]; exact Int.emod_nonneg _ (by decide))
  have v1 : (x + ζ * y).val = (x.val + (ζ * y).val) % 3329 := val_add' _ _
  have v2 : (x - ζ * y).val = (x.val + (3329 - (ζ * y).val)) % 3329 := val_sub' _ _
  rw [v1, v2]
  rw [c1, ai, ht] at n1
  rw [c2, ai, ht] at n2
  generalize (ζ * y).val = Z at *
  generalize x.val = X at *
  constructor <;> omega_using [n1, n2, hx, hzy]

/-- The two words of a butterfly of Algorithm 10 (`vibfly`): `x + y` and
`ζ (y - x)`. -/
theorem ibflyW {a b z : BitVec 16} {x y ζ : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hz : z.toNat = ζ.val * 65536 % 3329) :
    (csubW (a + b)).toNat = (x + y).val ∧ (caddW (montW (b - a) z)).toNat = (ζ * (y - x)).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  have p1 : -32768 ≤ a.toInt + b.toInt := by rw [ai, bi]; omega
  have p2 : a.toInt + b.toInt < 32768 := by rw [ai, bi]; omega
  have m1 : -32768 ≤ b.toInt - a.toInt := by rw [ai, bi]; omega
  have m2 : b.toInt - a.toInt < 32768 := by rw [ai, bi]; omega
  have c1 := csubW_spec (d := a + b) (by rw [toInt_add16 p1 p2, ai, bi]; omega)
    (by rw [toInt_add16 p1 p2, ai, bi]; omega)
  rw [toInt_add16 p1 p2, ai, bi] at c1
  have n1 := toNat_of_toInt (a := csubW (a + b)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  rw [c1] at n1
  have hm := mulZ_spec (b := b - a) (y := y - x) (ζ := ζ) (by rw [toInt_sub16 m1 m2, ai, bi]; omega)
    (by rw [toInt_sub16 m1 m2, ai, bi]; omega)
    (by
      have v : (y - x).val = (y.val + (3329 - x.val)) % 3329 := val_sub' _ _
      rw [toInt_sub16 m1 m2, ai, bi, v]; omega) hz
  have hzy := val_lt (ζ * (y - x))
  have n2 := toNat_of_toInt (a := caddW (montW (b - a) z)) (by rw [hm]; exact Int.natCast_nonneg _)
  rw [hm] at n2
  have v1 : (x + y).val = (x.val + y.val) % 3329 := val_add' _ _
  rw [v1]
  generalize (ζ * (y - x)).val = Z at *
  generalize x.val = X at *
  generalize y.val = Y at *
  constructor <;> omega_using [n1, n2, hx, hy]

end VG.Proof.MlKem.X86_64.W
