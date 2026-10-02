import VerifiedGarbage.Proof.Ed25519.X86.FieldMemory
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-! Field programs and exact Edwards-coordinate formulas. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open Fin.CommRing

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : BitVec 32) : Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : Env) (o a b i : Slot) :
    evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_add_apply (e : Env) (o a b i : Slot) :
    evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : Env) (o a b i : Slot) :
    evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure FieldKeep (x : BitVec 32) (s t : State) : Prop where
  keep : Keep s t
  frame : Frame [sub x 64 864] s.mem t.mem

theorem FieldKeep.refl (x : BitVec 32) (s : State) : FieldKeep x s s :=
  ⟨Keep.refl _, Frame.refl _ _⟩

theorem FieldKeep.trans {x : BitVec 32} {s t u : State}
    (h : FieldKeep x s t) (k : FieldKeep x t u) : FieldKeep x s u :=
  ⟨h.keep.trans k.keep, h.frame.trans k.frame⟩

theorem FieldKeep.ctx {x : BitVec 32} {s t : State}
    (h : FieldKeep x s t) (hc : Ctx x s) : Ctx x t := h.keep.ctx hc

theorem offset_inj {a b : Slot} (h : offset a = offset b) : a = b := by
  apply Fin.ext
  simp only [offset] at h
  omega

theorem restrict_update (e : Nat → Spec.X25519.Fe) (o : Slot) (v : Spec.X25519.Fe) :
    (fun i : Slot => Function.update e (offset o) v (offset i)) =
      Function.update (fun i : Slot => e (offset i)) o v := by
  funext i
  by_cases hi : i = o
  · subst i; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (offset_inj h))]

theorem const_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32) (o : Slot)
    (hf : Frame [sub x (offset o) 32] m m') :
    env m' x = Function.update (env m x) o (F m' x (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst i; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne hi]
    apply congrArg VG.Proof.X25519.toFe
    exact fe_frame1 hf hx (by simp only [offset]; omega)
      (by simp only [offset]; omega) (slot_ne (slot_valid o) (slot_valid i) (fun h => hi (offset_inj h)))

theorem raw_field_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (op : Op)
    (hv : opValid 64 op = true) (o : Slot) (ho : opOut op = offset o) :
    WP isa (.block op.code) s fun t => FieldKeep x s t ∧
      env t.mem x = Function.update (env s.mem x) o (opVal op (F s.mem x)) := by
  refine WP.mono (op_ok hc op hv) fun t ⟨hk, hf, he⟩ => ?_
  refine ⟨⟨hk, hf⟩, ?_⟩
  have hr := restrict_update (F s.mem x) o (opVal op (F s.mem x))
  funext i
  change F t.mem x (offset i) = Function.update (fun j => F s.mem x (offset j)) o (opVal op (F s.mem x)) i
  rw [← congrFun hr i]
  exact (he (offset i) (slot_valid i)).trans (by rw [ho])

theorem fieldOp_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (op : FieldOp) :
    WP isa (.block op.code) s fun t => FieldKeep x s t ∧ env t.mem x = evalOp op (env s.mem x) := by
  cases op with
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hk, hf, hv⟩ => ?_
    refine ⟨⟨hk, frameWiden hf hc.fit (by simp only [offset]; omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega)⟩, ?_⟩
    rw [const_env hc.fit o hf, hv]; rfl
  | copy o a =>
    exact raw_field_ok hc (.copy (offset o) (offset a))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | mul o a b =>
    exact raw_field_ok hc (.mul (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | add o a b =>
    exact raw_field_ok hc (.add (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | sub o a b =>
    exact raw_field_ok hc (.sub (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl

theorem fieldCode_ok (ops : List FieldOp) {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block (fieldCode ops)) s fun t =>
      FieldKeep x s t ∧ env t.mem x = evalOps ops (env s.mem x) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOp_ok hc op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) :
    point (evalOps pointAddOps e) 0 1 2 3 = addResult e 4 (by decide) := by
  rfl

theorem pointDouble_formula (e : Env) :
    point (evalOps pointDoubleOps e) 0 1 2 3 = addResult e 0 (by decide) := by
  rfl

theorem addResult_eq (e : Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    addResult e q hq = Spec.Ed25519.pointAdd (point e 0 1 2 3)
      (point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> ring

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) :=
  (pointAdd_formula e).trans (addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) :=
  (pointDouble_formula e).trans (addResult_eq e 0 (by decide) hd)

end VG.Proof.Ed25519.X86
