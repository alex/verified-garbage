import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.Block

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem vreg_inj (a b : Fin 16) : vreg a = vreg b ↔ a = b :=
  (show ∀ a b : Fin 16, vreg a = vreg b ↔ a = b by decide) a b

theorem vreg_ne (a : Fin 16) : vreg a ≠ .v31 :=
  (show ∀ a : Fin 16, vreg a ≠ .v31 by decide) a

theorem vreg_ne30 (a : Fin 16) : vreg a ≠ .v30 :=
  (show ∀ a : Fin 16, vreg a ≠ .v30 by decide) a

def Holds (vs : Nat → CState) (s : State) : Prop :=
  ∀ k : Fin 16, ∀ j, j < 4 → vword (s.v (vreg k)) j = (vs j)[k]

structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Same.trans {s₀ s₁ s₂ : State} (h : Same s₀ s₁) (h' : Same s₁ s₂) : Same s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

structure RoundSame (s s' : State) : Prop extends Same s s' where
  v30 : s'.v .v30 = s.v .v30

theorem RoundSame.trans {s₀ s₁ s₂ : State} (h : RoundSame s₀ s₁) (h' : RoundSame s₁ s₂) :
    RoundSame s₀ s₂ := ⟨h.toSame.trans h'.toSame, h'.v30.trans h.v30⟩

def step (v : CState) : Op → CState
  | .add d a b => v.set d (v[a] + v[b])
  | .xorRol d a b n => v.set d ((v[a] ^^^ v[b]).rotateLeft n)

theorem get_set (v : CState) (d k : Fin 16) (x : Word) :
    (v.set d x)[k] = if k = d then x else v[k] := by
  simp only [Vector.getElem_set, Fin.getElem_fin, Fin.ext_iff, eq_comm]

theorem op_ok (op : Op) {vs : Nat → CState} {s : State} (h : Holds vs s) (ht : s.v .v30 = rol8Table) :
    WP isa (.block op.code) s fun s' => Holds (fun j => step (vs j) op) s' ∧ RoundSame s s' := by
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, step, get_set, vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    by_cases h16 : n.val = 16
    · apply WP.of_runBlock
      simp only [Op.code, h16, ite_true, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
      split
      · rw [vword_rev32h_rol16 _ hj, Neon.vword_xor, h a j hj, h b j hj, h16]
      · exact h k j hj
    by_cases h8 : n.val = 8
    · apply WP.of_runBlock
      simp (config := {decide := true}) only [Op.code, h8, ite_true, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
      split
      · rw [ht, vword_tbl_rol8 _ hj, Neon.vword_xor, h a j hj, h b j hj, h8]
      · exact h k j hj
    have hn : n.val < 32 := n.isLt
    have hsh : VShiftOp.ushr.ok VArr.s4.esize (32 - n.val) = true := by
      simp only [VShiftOp.ok, VArr.esize, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hsl : VShiftOp.sli.ok VArr.s4.esize n.val = true := by
      simp only [VShiftOp.ok, VArr.esize, decide_eq_true_eq]; exact hn
    apply WP.of_runBlock
    simp only [Op.code, h16, h8, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      hsh, hsl, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
      RegUpd.v_setV, vreg_ne, Ne.symm (vreg_ne d), ite_false]
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, vword_map2 _ _ _ hj]
      simp only [VShiftOp.eval, Neon.shr_mask _ n hn, Neon.vword_xor,
        h a j hj, h b j hj, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn, BitVec.or_comm]
    · exact h k j hj

theorem ops_ok : ∀ (ops : List Op) {vs : Nat → CState} {s : State}, Holds vs s → s.v .v30 = rol8Table →
    WP isa (.block (ops.flatMap Op.code)) s fun s' =>
      Holds (fun j => ops.foldl step (vs j)) s' ∧ RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((op_ok op h ht).mono fun _ ⟨h', hs⟩ =>
      (ops_ok ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

/-- A term in the words `var k` of a state. -/
inductive E
  | var (k : Nat) | add (a b : E) | xor (a b : E) | rol (a : E) (n : Nat)
  deriving DecidableEq

def E.eval (v : CState) : E → Word
  | .var k => if h : k < 16 then v[k] else 0
  | .add a b => a.eval v + b.eval v
  | .xor a b => a.eval v ^^^ b.eval v
  | .rol a n => (a.eval v).rotateLeft n

/-- A state of terms. -/
abbrev ES := Nat → E

def ES.set (f : ES) (i : Nat) (x : E) : ES := fun k => if k = i then x else f k

/-- The scheduled operations on symbolic words. -/
def stepE (f : ES) : Op → ES
  | .add d a b => f.set d (.add (f a) (f b))
  | .xorRol d a b n => f.set d (.rol (.xor (f a) (f b)) n)

/-- `qround` on terms. -/
def qroundE (f : ES) (x y z w : Fin 16) : ES :=
  let a := E.add (f x) (f y); let d := E.rol (.xor (f w) a) 16
  let c := E.add (f z) d; let b := E.rol (.xor (f y) c) 12
  let a := E.add a b; let d := E.rol (.xor d a) 8
  let c := E.add c d; let b := E.rol (.xor b c) 7
  (((f.set x a).set y b).set z c).set w d

/-- The terms `f` evaluate to `v`, in the words of `v₀`. -/
def Rel (v₀ : CState) (f : ES) (v : CState) : Prop := ∀ k (hk : k < 16), (f k).eval v₀ = v[k]

theorem Rel.set {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) {i : Nat} (hi : i < 16) {x : E}
    {y : Word} (hx : x.eval v₀ = y) : Rel v₀ (f.set i x) (v.set i y hi) := by
  intro k hk
  simp only [ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem Rel.step {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (i : Op) :
    Rel v₀ (stepE f i) (step v i) := by
  cases i with
  | add d a b => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])
  | xorRol d a b n => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])

theorem Rel.foldl {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) :
    ∀ is : List Op, Rel v₀ (is.foldl stepE f) (is.foldl Neon4.step v)
  | [] => h
  | i :: is => (h.step i).foldl is

theorem Rel.qround {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (x y z w : Fin 16) :
    Rel v₀ (qroundE f x y z w) (qround v x y z w) := by
  simp only [qroundE]
  refine (((h.set x.2 ?_).set y.2 ?_).set z.2 ?_).set w.2 ?_ <;>
    simp only [E.eval, h _ x.2, h _ y.2, h _ z.2, h _ w.2, Fin.getElem_fin]

/-- The words of a state, as terms. -/
def vars : ES := .var

theorem rel_vars (v : CState) : Rel v vars v := fun k hk => by simp [vars, E.eval, hk]

theorem Rel.eq {v₀ : CState} {f : ES} {v v' : CState} (h : Rel v₀ f v) (h' : Rel v₀ f v') : v = v' :=
  Vector.ext fun k hk => (h k hk).symm.trans (h' k hk)

/-- Two states of terms agree on the words of a state. -/
def ES.eq16 (f g : ES) : Bool := (List.range 16).all fun k => f k == g k

theorem Rel.of_eq16 {v₀ : CState} {f g : ES} {v : CState} (h : Rel v₀ f v) (e : ES.eq16 f g = true) :
    Rel v₀ g v := by
  intro k hk
  simp only [ES.eq16, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e k hk]; exact h k hk

theorem cols_eq (v : CState) :
    (quarters cols).foldl step v =
      qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 := by
  have e : ES.eq16 ((quarters cols).foldl stepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 4 8 12).qround 1 5 9 13 |>.qround 2 6 10 14).qround 3 7 11 15)

theorem diags_eq (v : CState) :
    (quarters diags).foldl step v =
      qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := by
  have e : ES.eq16 ((quarters diags).foldl stepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 5 10 15).qround 1 6 11 12 |>.qround 2 7 8 13).qround 3 4 9 14)

theorem innerBlock_eq (v : CState) : (quarters cols ++ quarters diags).foldl step v = innerBlock v := by
  rw [List.foldl_append, cols_eq, diags_eq]; rfl


theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : Holds vs s) (ht : s.v .v30 = rol8Table) :
    WP isa (.block doubleRound) s fun s' =>
      Holds (fun j => innerBlock (vs j)) s' ∧ RoundSame s s' := by
  have e : (fun j => (quarters cols ++ quarters diags).foldl step (vs j)) =
      fun j => innerBlock (vs j) := funext fun j => innerBlock_eq (vs j)
  exact (ops_ok _ h ht).mono fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

theorem rounds_ok {vs : Nat → CState} {s : State} (h : Holds vs s) (ht : s.v .v30 = rol8Table) :
    ∀ n, WP isa (rounds n) s fun s' =>
      Holds (fun j => Nat.repeat innerBlock n (vs j)) s' ∧ RoundSame s s'
  | 0 => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | n + 1 => WP.seq ((rounds_ok h ht n).mono fun _ ⟨h', hs⟩ =>
      (doubleRound_ok h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Neon4

