import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Byte lanes of the RC4 code's vectors

The RC4 code's vectors are byte tables (the permutation, sixteen bytes per
register) and bytes broadcast to every lane (`bc`). These are the byte-lane
facts about the AdvSIMD instructions it uses.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64

/-- `b` in every byte. -/
def bc (b : BitVec 8) : BitVec 128 := ofVBytes fun _ => b

theorem vbyte_ext {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true,
    Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

theorem vbyte_bc (b : BitVec 8) {e : Nat} (he : e < 16) : vbyte (bc b) e = b :=
  vbyte_ofVBytes _ he

theorem vbyte_xor (x y : BitVec 128) (e : Nat) : vbyte (x ^^^ y) e = vbyte x e ^^^ vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_or (x y : BitVec 128) (e : Nat) : vbyte (x ||| y) e = vbyte x e ||| vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_not (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (~~~x) e = ~~~vbyte x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    show 8 * e + i < 128 by omega]

theorem bc_xor (a b : BitVec 8) : bc a ^^^ bc b = bc (a ^^^ b) :=
  vbyte_ext fun e he => by rw [vbyte_xor, vbyte_bc _ he, vbyte_bc _ he, vbyte_bc _ he]

theorem bc_or (a b : BitVec 8) : bc a ||| bc b = bc (a ||| b) :=
  vbyte_ext fun e he => by rw [vbyte_or, vbyte_bc _ he, vbyte_bc _ he, vbyte_bc _ he]

theorem vbyte_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 16) : vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) := by
  simp only [VArr.map2]
  exact vbyte_ofVBytes _ he

theorem add_bc (a b : BitVec 8) : VArr.b16.map2 (fun _ x y => x + y) (bc a) (bc b) = bc (a + b) :=
  vbyte_ext fun e he => by rw [vbyte_map2 _ _ _ he, vbyte_bc _ he, vbyte_bc _ he, vbyte_bc _ he]

theorem sub_bc (a b : BitVec 8) : VArr.b16.map2 (fun _ x y => x - y) (bc a) (bc b) = bc (a - b) :=
  vbyte_ext fun e he => by rw [vbyte_map2 _ _ _ he, vbyte_bc _ he, vbyte_bc _ he, vbyte_bc _ he]

/-- CMEQ's mask, byte by byte. -/
theorem vbyte_cmeq (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0) x y) e =
      if vbyte x e = vbyte y e then BitVec.allOnes 8 else 0 :=
  vbyte_map2 _ _ _ he

/-- BIT, byte by byte, for a mask of all-zero and all-one bytes. -/
theorem vbyte_bit (d n m : BitVec 128) {e : Nat} (c : Prop) [Decidable c]
    (hm : vbyte m e = if c then BitVec.allOnes 8 else 0) :
    vbyte (VSelOp.bit.eval d n m) e = if c then vbyte n e else vbyte d e := by
  by_cases hc : c
  · simp only [hc, ite_true] at hm ⊢
    simp only [VSelOp.eval, vbyte_xor, vbyte_and, hm, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
  · simp only [hc, ite_false] at hm ⊢
    simp [VSelOp.eval, vbyte_xor, vbyte_and, hm]

/-- A byte replaced. -/
theorem vbyte_setLane (x : BitVec 128) (v : BitVec 8) {i e : Nat} (hi : i < 16) (he : e < 16) :
    vbyte (setLane x 8 i v) e = if e = i then v else vbyte x e := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hk, decide_true, Bool.true_and, show 8 * e + k < 128 by omega]
  by_cases h : e = i
  · subst h
    simp [show ¬ 8 * e + k < 8 * e by omega, show 8 * e + k - 8 * e = k by omega, hk,
      show k < 128 by omega]
  · simp only [h, ite_false]
    rcases (by omega : e < i ∨ i < e) with h' | h'
    · simp [show 8 * e + k < 8 * i by omega]
      intro; omega
    · simp [show ¬ 8 * e + k < 8 * i by omega, show ¬ 8 * e + k - 8 * i < 8 by omega,
        BitVec.getLsbD_of_ge v (8 * e + k - 8 * i) (by omega), hk]

theorem ite_iff {α : Type} {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = if q then a else b := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

theorem extract_byte (x : BitVec 128) (j : Nat) : x.extractLsb' (8 * j) 8 = vbyte x j := rfl

open RegUpd in
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.read, addr, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
        RegUpd.wr_setV, RegUpd.v_setV,
        VOp.eval, Size.bits, BitVec.setWidth_eq, BitVec.shiftLeft_zero,
        BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_width_append,
        BitVec.cast_eq, Option.bind_some, Option.map_some, Option.some.injEq,
        exists_eq_left', ite_true, ite_false, reduceCtorEq,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, true_and, and_true, $ls,*]))

end VG.Proof.Rc4.AArch64
