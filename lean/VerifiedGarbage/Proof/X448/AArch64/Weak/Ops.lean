import VerifiedGarbage.Proof.X448.AArch64.Weak.Env

/-!
# X448 on AArch64: sequences of field operations

Untrusted: everything here is checked by Lean. Slot-indexed operations
interpret the implementation's field-operation lists as environment updates.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Impl.X448.AArch64.Weak

inductive FieldOp
  | mul (o a b : Index)
  | add (o a b : Index)
  | sub (o a b : Index)
  | mulSmall (o a : Index)
  | copy (o a : Index)
  deriving DecidableEq

def FieldOp.impl : FieldOp → Impl.X448.AArch64.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .add o a b => .add (slot o.val) (slot a.val) (slot b.val)
  | .sub o a b => .sub (slot o.val) (slot a.val) (slot b.val)
  | .mulSmall o a => .mulSmall (slot o.val) (slot a.val)
  | .copy o a => .copy (slot o.val) (slot a.val)

def FieldOp.apply : FieldOp → Env → Env
  | .mul o a b => opMul o a b
  | .add o a b => opAdd o a b
  | .sub o a b => opSub o a b
  | .mulSmall o a => opA24 o a
  | .copy o a => opCopy o a

def applyOps : List FieldOp → Env → Env
  | [], e => e
  | op :: rest, e => applyOps rest (op.apply e)

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (op : FieldOp) :
    WP isa (Impl.X448.AArch64.Weak.code op.impl) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = op.apply (E s.mem base) := by
  cases op with
  | mul o a b => exact mulE hs hb o a b
  | add o a b => exact addE hs hb o a b
  | sub o a b => exact subE hs hb o a b
  | mulSmall o a => exact a24E hs hb o a
  | copy o a => exact copyE hs hb o a

theorem ops_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (xs : List FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = applyOps xs (E s.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op rest ih =>
    change WP isa (.seq (Impl.X448.AArch64.Weak.code op.impl) (ops (rest.map FieldOp.impl))) s _
    rw [WP.seq_iff]
    refine WP.mono (fieldOp_ok hs hb op) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, ?_⟩
    rw [ue, te]
    rfl

/-- The arithmetic part of one Montgomery-ladder step. -/
def stepFields : List FieldOp :=
  [.add 5 1 2, .mul 9 5 5, .sub 6 1 2, .mul 10 6 6, .sub 11 9 10,
    .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
    .add 3 12 13, .mul 3 3 3, .sub 4 12 13, .mul 4 4 4, .mul 4 0 4,
    .mul 1 9 10, .mulSmall 2 11, .add 2 9 2, .mul 2 11 2]

theorem stepFields_impl : stepFields.map FieldOp.impl = stepOps := by decide +kernel

end VG.Proof.X448.AArch64.Weak
