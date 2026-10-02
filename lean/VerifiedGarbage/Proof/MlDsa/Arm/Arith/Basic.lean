import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlDsa.Arith.Mul32
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: the values of the arithmetic modulo `q`

What the pieces of code of `Impl/MlDsa/Arm/Arith/Common.lean` compute, as
functions on words (`bred`, `bfix`, `bcsub`, `bmulz`), and their values
(`bcsub_mulz`: `csub` after `mulz` is the product modulo `q`), from the
arithmetic of `Proof/MlDsa/Arith/Mul32.lean`; and the symbolic execution of
`mulz`, once for any state (`mulz_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-! ## Words -/

/-- `q` as a word. -/
abbrev Qw : BitVec 32 := 8380417

theorem loadQ_val : ((0x7F : BitVec 16) ++ ((0xE001 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = Qw := by
  decide

/-- What `red d t Q` leaves in `d`. -/
def bred (x : BitVec 32) : BitVec 32 := x - x >>> 23 * Qw

/-- What `fixup d t Q` leaves in `d`. -/
def bfix (y : BitVec 32) : BitVec 32 := y + y >>> 31 * Qw

/-- What `csub d t Q` leaves in `d`. -/
def bcsub (x : BitVec 32) : BitVec 32 := bfix (x - Qw)

/-- What `mulz acc b t` leaves in `acc`, for the pieces `z₂`, `z₁`, `z₀`. -/
def bmulz (b z₂ z₁ z₀ : BitVec 32) : BitVec 32 := bred (b * z₀ + bred (b * z₁ + bred (b * z₂) <<< 7) <<< 7)

theorem bred_toNat (x : BitVec 32) : (bred x).toNat = red23 x.toNat := by
  unfold bred red23
  rw [q_eq]
  bv_omega

theorem bcsub_toNat {x : BitVec 32} (h : x.toNat < 2 * q) : (bcsub x).toNat = x.toNat % q := by
  unfold bcsub bfix
  rw [q_eq] at *
  by_cases h' : x.toNat < 8380417
  · rw [Nat.mod_eq_of_lt h']; bv_omega
  · bv_omega

/-- `fixup (a - b)`: the difference of reduced values, reduced. -/
theorem bfix_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (bfix (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  unfold bfix
  rw [q_eq] at *
  by_cases h' : b.toNat ≤ a.toNat
  · bv_omega
  · bv_omega

/-- `csub (a + b)`: the sum of reduced values, reduced. -/
theorem bcsub_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (bcsub (a + b)).toNat = (a.toNat + b.toNat) % q := by
  have : (a + b).toNat = a.toNat + b.toNat := by rw [q_eq] at *; bv_omega
  rw [bcsub_toNat (by omega), this]

theorem pieces_toNat (a : BitVec 32) :
    (a >>> 14).toNat = a.toNat / 16384 ∧ ((a <<< 18) >>> 25).toNat = a.toNat / 128 % 128 ∧
      ((a <<< 25) >>> 25).toNat = a.toNat % 128 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem bmulz_toNat {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < 2 ^ 23) :
    (bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25)).toNat = mulzN b.toNat a.toNat := by
  obtain ⟨p2, p1, p0⟩ := pieces_toNat a
  obtain ⟨h1, h2, h3, -⟩ := mulzN_bounds hb ha
  have m2 : (b * (a >>> 14)).toNat = b.toNat * (a.toNat / 16384) := by
    rw [BitVec.toNat_mul, p2, Nat.mod_eq_of_lt h1]
  have e1 : (bred (b * (a >>> 14))).toNat = mulz1 b.toNat a.toNat := by rw [bred_toNat, m2]; rfl
  have s1 : (b * ((a <<< 18) >>> 25) + bred (b * (a >>> 14)) <<< 7).toNat =
      b.toNat * (a.toNat / 128 % 128) + mulz1 b.toNat a.toNat * 128 := by
    have hr : mulz1 b.toNat a.toNat ≤ redMax := red23_le h1
    unfold redMax at hr
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, e1, p1, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 7 = 128 from rfl]
    have hm : b.toNat * (a.toNat / 128 % 128) < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (a := mulz1 b.toNat a.toNat * 128) (by omega)]
    exact Nat.mod_eq_of_lt h2
  have e2 : (bred (b * ((a <<< 18) >>> 25) + bred (b * (a >>> 14)) <<< 7)).toNat = mulz2 b.toNat a.toNat := by
    rw [bred_toNat, s1]; rfl
  have s2 : (b * ((a <<< 25) >>> 25) + bred (b * ((a <<< 18) >>> 25) + bred (b * (a >>> 14)) <<< 7) <<< 7).toNat =
      b.toNat * (a.toNat % 128) + mulz2 b.toNat a.toNat * 128 := by
    have hr : mulz2 b.toNat a.toNat ≤ redMax := red23_le h2
    unfold redMax at hr
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, e2, p0, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 7 = 128 from rfl]
    have hm : b.toNat * (a.toNat % 128) < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (a := mulz2 b.toNat a.toNat * 128) (by omega)]
    exact Nat.mod_eq_of_lt h3
  unfold bmulz
  rw [bred_toNat, s2]; rfl

/-- `csub` after `mulz`: the product of `b` and `a`, reduced. -/
theorem bcsub_mulz {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < q) :
    (bcsub (bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25))).toNat = b.toNat * a.toNat % q := by
  have ha' : a.toNat < 2 ^ 23 := by rw [q_eq] at ha; omega
  have := (mulzN_bounds hb ha').2.2.2
  rw [bcsub_toNat (by rw [bmulz_toNat hb ha']; exact Nat.lt_of_le_of_lt this redMax_lt), bmulz_toNat hb ha',
    mulzN_mod]

/-- `mulz` is less than `2q`. -/
theorem bmulz_le {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < q) :
    (bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25)).toNat ≤ redMax := by
  have ha' : a.toNat < 2 ^ 23 := by rw [q_eq] at ha; omega
  rw [bmulz_toNat hb ha']; exact (mulzN_bounds hb ha').2.2.2

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

theorem toNat_val (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-! ## Registers kept -/

/-- `s'` has the registers `rs`, and the regions and stack pointer, of `s`. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r ∈ rs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keep_iff {rs : List Reg} {s s' : State} :
    Keep rs s s' ↔ (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨fun h => ⟨h.gpr, h.rd, h.wr, h.sp⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The lemmas that prove `Keep` after a symbolic execution (`run_block`). -/
macro "keep_simp" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp (config := {decide := true}) only [keep_iff, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true, true_and, ite_true, ite_false]))

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs', r ∈ rs) :
    Keep rs' s s' :=
  ⟨fun r hr => h.gpr r (hs r hr), h.rd, h.wr, h.sp⟩

/-! ## `mulz`, symbolically -/

/-- What `mulz .r9 .r8 .r12` does: `r9` becomes the product, `r12` is
clobbered, and nothing else changes. -/
theorem mulz_ok {s : State} {b z₂ z₁ z₀ : BitVec 32} (h4 : s.gpr .r4 = Qw) (h5 : s.gpr .r5 = z₂)
    (h6 : s.gpr .r6 = z₁) (h7 : s.gpr .r7 = z₀) (h8 : s.gpr .r8 = b) :
    WP isa (.block (mulz .r9 .r8 .r12)) s fun s' =>
      s'.gpr .r9 = bmulz b z₂ z₁ z₀ ∧ (∀ r, r ≠ .r9 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [mulz, red, bmulz, bred, h4, h5, h6, h7, h8]
  exact ⟨trivial, fun r h9 h12 => by simp [h9, h12], trivial⟩

end VG.Proof.MlDsa.Arm.Arith
