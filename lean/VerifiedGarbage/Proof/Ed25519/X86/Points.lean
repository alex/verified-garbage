import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86.Field

/-! Exact extended-coordinate operations and the slots they preserve. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .add o _ _ | .sub o _ _ => o

theorem evalOp_unchanged (op : FieldOp) (e : Env) (i : Slot) (hi : i ≠ fieldDest op) :
    evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ fieldDest op) : evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change evalOps ops (evalOp op e) i = e i
    rw [ih (evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (fieldDest op).val < 16)
    (e : Env) (i : Slot) (hi : 16 ≤ i.val) : evalOps ops e i = e i := by
  apply evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem pointAdd_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddOps e i = e i :=
  point_ops_high _ (by decide) e i hi

theorem pointDouble_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointDoubleOps e i = e i :=
  point_ops_high _ (by decide) e i hi

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : Env) :
    point (evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

theorem savePoint_eval (e : Env) :
    point (evalOps savePointOps e) 17 18 19 20 = point e 0 1 2 3 := rfl

theorem restorePoint_eval (e : Env) :
    point (evalOps restorePointOps e) 0 1 2 3 = point e 17 18 19 20 := rfl

theorem copyPointToQ_eval (e : Env) :
    point (evalOps copyPointToQOps e) 4 5 6 7 = point e 0 1 2 3 := rfl

theorem pointDouble_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointDouble) s fun t =>
      FieldKeep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointDoubleOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointDouble_eval _ hd, pointDouble_high _⟩

theorem pointAdd_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointAdd) s fun t =>
      FieldKeep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointAddOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAdd_eval _ hd, pointAdd_high _⟩

end VG.Proof.Ed25519.X86
