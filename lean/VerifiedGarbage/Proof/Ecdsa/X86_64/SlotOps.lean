import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-!
# ECDSA on x86-64: field operations on numbered slots

The Montgomery operations of `Proof/Mont/X86_64/Ops.lean` on the slots
`c.sl i` of the working space, modulo `p` (`c.MP'`) or `n` (`c.MN'`): an
operation writing slot `o` keeps every other slot but the temporary area's
(`sv_keep`) and the moduli (`ModOk.keep`); and what a slot stands for after
a multiplication by `1` or by `R² mod m` (`toM_one_mul`, `toM_r2`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem MP'_n (c : Cfg) : c.MP'.n = c.n := rfl
theorem MN'_n (c : Cfg) : c.MN'.n = c.n := rfl
theorem MP'_tmp (c : Cfg) : c.MP'.tmp = c.sl TMP := rfl
theorem MN'_tmp (c : Cfg) : c.MN'.tmp = c.sl TMP := rfl
theorem MP'_mo (c : Cfg) : c.MP'.mo = c.sl MP := rfl
theorem MN'_mo (c : Cfg) : c.MN'.mo = c.sl MN := rfl

/-- A slot apart from what an operation writes keeps its number. -/
theorem sv_keep {M : Mod} (hMn : M.n = c.n) (hMt : M.tmp = c.sl TMP) (h7 : c.n < 7)
    {base : Addr} (hn : base.toNat + size ≤ 2 ^ 64) {o : Nat} {s s' : State}
    (h : OpKeep M base (c.sl o) s s') {i : Nat} (hi : i < 45) (hio : i ≠ o) (hit : i ≠ TMP) :
    sv c base s' i = sv c base s i := by
  have hl := sl_le c h7 hi
  refine h.unch.wordsVal (fun w hw => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [hMn]; exact sl_apart c hio
  · rw [hMn, hMt]; exact sl_apart c hit

/-- The modulus in slot `j` survives an operation writing another slot. -/
theorem _root_.VG.Proof.Mont.X86_64.ModOk.keep {M M' : Mod} {m : Nat} {base : Addr} {s s' : State}
    (hM : ModOk M size m s.mem base) {j : Nat} (hj : j < 45) (hmo : M.mo = c.sl j) (hMn : M.n = c.n)
    (hM'n : M'.n = c.n) (hM't : M'.tmp = c.sl TMP) (h7 : c.n < 7) (hn : base.toNat + size ≤ 2 ^ 64)
    {o : Nat} (h : OpKeep M' base (c.sl o) s s') (hjo : j ≠ o) (hjt : j ≠ TMP) :
    ModOk M size m s'.mem base :=
  ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by
    have := sv_keep hM'n hM't h7 hn h hj hjo hjt
    simp only [sv] at this
    rw [hmo, hMn, this, ← hMn, ← hmo]; exact hM.val, hM.inv⟩

/-- `[o] = [a] [b] R⁻¹ mod m`, on slots. -/
theorem slMul_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (h7 : c.n < 7) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hB : sv c base s b < m) :
    WP isa (.block (mul M (c.sl o) (c.sl a) (c.sl b))) s fun s' => OpKeep M base (c.sl o) s s' ∧
      sv c base s' o < m ∧ sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  have := mul_ok hs hM (o := c.sl o) (a := c.sl a) (b := c.sl b) (by rw [hMn]; exact sl_le c h7 ho)
    (by rw [hMn]; exact sl_le c h7 ha) (by rw [hMn]; exact sl_le c h7 hb) (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

/-- `[o] = ([a] + [b]) mod m`, on slots. -/
theorem slAdd_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (h7 : c.n < 7) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hAB : sv c base s a + sv c base s b < 2 * m) :
    WP isa (.block (add M (c.sl o) (c.sl a) (c.sl b))) s fun s' => OpKeep M base (c.sl o) s s' ∧
      sv c base s' o = (sv c base s a + sv c base s b) % m := by
  have := add_ok hs hM (o := c.sl o) (a := c.sl a) (b := c.sl b) (by rw [hMn]; exact sl_le c h7 ho)
    (by rw [hMn]; exact sl_le c h7 ha) (by rw [hMn]; exact sl_le c h7 hb) (by rw [hMn]; exact hAB)
  rw [hMn] at this
  exact this

/-- A multiplication by `1` leaves Montgomery's form. -/
theorem toM_one_mul {m R r A : Nat} (hR : Nat.Coprime R m) (h : r * R % m = A * 1 % m) :
    (r : ZMod m) = toM m R A := by
  have h' : (r : ZMod m) * R = A := by
    have := (ZMod.natCast_eq_natCast_iff' (r * R) (A * 1) m).mpr h
    rwa [Nat.cast_mul, Nat.mul_one] at this
  have hu : (R : ZMod m) * (R : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hR
  unfold toM
  rw [← h', mul_assoc, hu, mul_one]

/-- A multiplication by `R² mod m` enters Montgomery's form. -/
theorem toM_r2 {m R r A : Nat} (hR : Nat.Coprime R m) (h : r * R % m = A * (R * R % m) % m) :
    toM m R r = (A : ZMod m) := by
  have h' : (r : ZMod m) * R = A * (R * R) := by
    have := (ZMod.natCast_eq_natCast_iff' (r * R) (A * (R * R % m)) m).mpr h
    rwa [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul] at this
  have hu : (R : ZMod m) * (R : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hR
  unfold toM
  have : (r : ZMod m) = A * R := by
    have e : (r : ZMod m) * R * (R : ZMod m)⁻¹ = A * (R * R) * (R : ZMod m)⁻¹ := by rw [h']
    rwa [mul_assoc, hu, mul_one, mul_assoc, mul_assoc, hu, mul_one] at e
  rw [this, mul_assoc, hu, mul_one]

/-- What `x R mod m` stands for. -/
theorem toM_mont {m R x : Nat} (hR : Nat.Coprime R m) : toM m R (x * R % m) = (x : ZMod m) := by
  unfold toM
  rw [ZMod.natCast_mod, Nat.cast_mul, mul_assoc, ZMod.coe_mul_inv_eq_one R hR, mul_one]

end VG.Proof.Ecdsa.X86_64
