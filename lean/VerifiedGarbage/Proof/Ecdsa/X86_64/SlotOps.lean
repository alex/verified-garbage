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
theorem toM_one_mul {m R r A : Nat} [NeZero m] (hR : UnitMod m R) (h : r * R % m = A * 1 % m) :
    Fin.ofNat m r = toM m R A := by
  have h' : Fin.ofNat m r * Fin.ofNat m R = Fin.ofNat m A := by
    rw [← ofNat_mul', ofNat_eq_ofNat, h, Nat.mul_one]
  have hu := mul_rinv hR
  unfold toM
  grind

/-- A multiplication by `R² mod m` enters Montgomery's form. -/
theorem toM_r2 {m R r A : Nat} [NeZero m] (hR : UnitMod m R) (h : r * R % m = A * (R * R % m) % m) :
    toM m R r = Fin.ofNat m A := by
  have h' : Fin.ofNat m r * Fin.ofNat m R = Fin.ofNat m A * (Fin.ofNat m R * Fin.ofNat m R) := by
    rw [← ofNat_mul', ← ofNat_mul', ← ofNat_mul', ofNat_eq_ofNat, h, Nat.mul_mod, Nat.mod_mod,
      ← Nat.mul_mod]
  have hu := mul_rinv hR
  unfold toM
  grind

/-- What `x R mod m` stands for. -/
theorem toM_mont {m R x : Nat} [NeZero m] (hR : UnitMod m R) : toM m R (x * R % m) = Fin.ofNat m x := by
  unfold toM
  rw [ofNat_mod, ofNat_mul', Lean.Grind.Semiring.mul_assoc, mul_rinv hR, Lean.Grind.Semiring.mul_one]

/-- A number below `m` stands for zero only if it is zero. -/
theorem toM_eq_zero_iff {m R x : Nat} [NeZero m] (hR : UnitMod m R) (hx : x < m) :
    toM m R x = 0 ↔ x = 0 := by
  unfold toM
  constructor
  · intro h
    have hu := mul_rinv hR
    have h' : Fin.ofNat m x = 0 := by grind
    have := congrArg Fin.val h'
    rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hx] at this
  · rintro rfl
    exact Lean.Grind.Semiring.zero_mul _

end VG.Proof.Ecdsa.X86_64
