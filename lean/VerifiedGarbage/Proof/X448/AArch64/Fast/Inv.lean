import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder
import VerifiedGarbage.Proof.X448.AArch64.Weak.Inv

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. The addition chain of
`Impl/X448/AArch64/Weak.lean`, with the faster field operations.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok decCounter_ok opMul opCopy opSqn opMul_update
  FieldOp applyOps invEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x19 :: fclob) s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem IKeep.trans {base : Addr} {s t u : State} (h : IKeep base s t) (h' : IKeep base t u) :
    IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem FKeep.ikeep {base : Addr} {s t : State} (h : FKeep base s t) : IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → BEnv s.mem base → WP isa code s fun t =>
    IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = f (EV s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : ISpec base c₁ f) (h₂ : ISpec base c₂ g) :
    ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

/-- The inversion's operations: products and copies. -/
def fimpl : FieldOp → Impl.X448.AArch64.Fast.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .copy o a => .copy (slot o.val) (slot a.val)
  | _ => .copy 0 0

def MulCopy : FieldOp → Prop
  | .mul o a b => a = b ∨ o ≠ b
  | .copy .. => True
  | _ => False

theorem opsI (base : Addr) (xs : List FieldOp) (hx : ∀ x ∈ xs, MulCopy x) :
    ISpec base (Impl.X448.AArch64.Fast.ops (xs.map fimpl)) (applyOps xs) := by
  induction xs with
  | nil => exact fun s _ hb => WP.block_nil ⟨⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩, hb, rfl⟩
  | cons x xs ih =>
    intro s hs hb
    have ih' := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    refine WP.seq ?_
    cases x with
    | mul o a b =>
      refine WP.mono (fmulE hs hb o a b (hx _ List.mem_cons_self)) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | copy o a =>
      refine WP.mono (copyE hs hb o a) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | _ => exact absurd (hx _ List.mem_cons_self) (by simp [MulCopy])

theorem sqnI (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    ISpec base (Impl.X448.AArch64.Fast.sqn (slot o.val) n) (opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.AArch64.Fast.sqn, WP.seq_iff]
  refine WP.mono (setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : IKeep base s t := counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ IKeep base s u ∧ BEnv u.mem base ∧
    u.gpr .x19 = BitVec.ofNat 64 m ∧
    EV u.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.block_append_iff]
    have hsq : Impl.Curve448.AArch64.Fast.sqr (slot o.val) (slot o.val) =
        Impl.X448.AArch64.Fast.fmul (slot o.val) (slot o.val) (slot o.val) := by
      simp only [Impl.X448.AArch64.Fast.fmul, ite_true]
    rw [hsq]
    refine WP.mono (fmulE (ku.scr hs) bu o o o (Or.inl rfl)) fun v ⟨kv, bv, _, _, ev⟩ => ?_
    have cv : v.gpr .x19 = BitVec.ofNat 64 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : IKeep base s w := ku.trans (kv.ikeep.trans (counter_keep wg wm wr ww))
    have bw : BEnv w.mem base := wm ▸ bv
    have ew : EV w.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m)) := by
      rw [wm, ev, eu]
      simp only [VG.Proof.X448.AArch64.opMul, Function.update_self, Function.update_idem]
      rw [← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, State.read, BitVec.setWidth_eq, bne, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

theorem invert_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.invert invEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 2] (by simp [MulCopy])).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 2, .copy 15 14] (by simp [MulCopy])).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15] (by simp [MulCopy])).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16] (by simp [MulCopy])).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17] (by simp [MulCopy])).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18] (by simp [MulCopy])).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 21 20] (by simp [MulCopy])).seq <|
    (sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 2] (by simp [MulCopy])).seq <|
    (sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 2, .mul 21 21 20] (by simp [MulCopy]))
  exact h

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa Impl.X448.AArch64.Fast.invert s fun t =>
      IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = invEnv (EV s.mem base) :=
  invert_spec base s hs hb

end VG.Proof.X448.AArch64.Fast
