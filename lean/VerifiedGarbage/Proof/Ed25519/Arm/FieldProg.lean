import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-! Compositional field programs and the extended Edwards formulas. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open Fin.CommRing

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (b : BitVec 32) : Env := fun i => FS m (State.addr b) (offset i)

def AllLim (m : Mem) (b : BitVec 32) : Prop := ∀ i : Slot, Lim m (State.addr b) (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure Keep (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest clob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : BitVec 32) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : BitVec 32} {s t u : State} (h : Keep b s t) (k : Keep b t u) :
    Keep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : BitVec 32} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

theorem limb_slot_frame {b : BitVec 32} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m') :
    ∀ k < 16, limb m' (State.addr b) (offset i) k = limb m (State.addr b) (offset i) k := by
  have hi := slot_range i
  have ho := slot_range o
  have hsep : offset i + 64 ≤ offset o ∨ offset o + 64 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega
  rw [ACC_eq] at hi ho
  refine limb_frame hf fun r hr k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by rw [ACC_eq]; omega)) (by omega) (by rw [ACC_eq]; omega)

theorem field_update {b : BitVec 32} {m m' : Mem} (o : Slot) (hl : AllLim m b)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m')
    (ho : Lim m' (State.addr b) (offset o)) :
    AllLim m' b ∧ env m' b = Function.update (env m b) o (FS m' (State.addr b) (offset o)) := by
  constructor
  · intro i
    by_cases hi : i = o
    · subst hi; exact ho
    · intro k hk
      rw [limb_slot_frame hi hf k hk]
      exact hl i k hk
  · funext i
    by_cases hi : i = o
    · subst hi; simp only [Function.update_self, env]
    · rw [Function.update_of_ne hi]
      exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_slot_frame hi hf))

theorem field_finish {b : BitVec 32} {s t : State} (o : Slot) (hl : AllLim s.mem b)
    (hr : Rest clob s t)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem)
    (ho : Lim t.mem (State.addr b) (offset o)) {v : Spec.X25519.Fe}
    (hv : FS t.mem (State.addr b) (offset o) = v) :
    Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = Function.update (env s.mem b) o v := by
  obtain ⟨hlim, he⟩ := field_update o hl hf ho
  rw [hv] at he
  exact ⟨⟨hr, frame_FA (slot_range o) hf⟩, hlim, he⟩

theorem fieldOp_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (op : FieldOp) :
    WP isa op.code s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOp op (env s.mem b) := by
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o hf) ho hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o hf) ho hv
  | mul o a c =>
    refine WP.mono (mul_ok (slot_range o).2 (slot_range a).2 (slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl hr hf ho (VG.Proof.X25519.toFe_mul hv)
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl hr (frame_o hf) ho (VG.Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl hr (frame_o hf) ho (VG.Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    refine WP.mono (fieldOp_ok hc hl op) fun t ⟨ht, hlt, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc) hlt) fun u ⟨hu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hlu, by rw [eu, et]; rfl⟩

theorem constField_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o v := fieldOp_ok hc hl (.const o v)

theorem copyField_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a) := fieldOp_ok hc hl (.copy o a)

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

end VG.Proof.Ed25519.Arm
