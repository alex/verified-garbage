import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.X448.Invert

/-!
# X448 on ARMv7: runs of squarings

The inversion reuses field multiplication in a loop with its own counter. The
field slots and memory frame compose exactly as they do for straight-line
operation lists.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.r11 :: workRegs) s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem IKeep.refl (base : Addr) (s : State) : IKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem IKeep.trans {base : Addr} {s t u : State} (h : IKeep base s t) (h' : IKeep base t u) :
    IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Keep.ikeep {base : Addr} {s t : State} (h : Keep base s t) : IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .r11 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → BoundedEnv s.mem base → WP isa code s fun t =>
    IKeep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = f (E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : ISpec base c₁ f) (h₂ : ISpec base c₂ g) :
    ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

theorem opsI (base : Addr) (xs : List FieldOp) :
    ISpec base (ops (xs.map FieldOp.impl)) (applyOps xs) := fun _ hs hb =>
  WP.mono (ops_ok hs hb xs) fun _ ⟨tk, tb, te⟩ => ⟨tk.ikeep, tb, te⟩

def opSqn (o : Index) (n : Nat) (e : Env) : Env := Function.update e o (Proof.X448.sqn (e o) n)

theorem opMul_update (o : Index) (e : Env) (v : Spec.X448.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

theorem sqnI (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    ISpec base (Impl.X448.Arm.sqn (slot o.val) n) (opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.Arm.sqn, WP.seq_iff]
  refine WP.mono (setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : IKeep base s t := counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ IKeep base s u ∧ BoundedEnv u.mem base ∧
    u.gpr .r11 = BitVec.ofNat 32 m ∧
    E u.mem base = Function.update (E s.mem base) o (Proof.X448.sqn (E s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.seq_iff]
    refine WP.mono (mulE (ku.scr hs) bu o o o) fun v ⟨kv, bv, ev⟩ => ?_
    have cv : v.gpr .r11 = BitVec.ofNat 32 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : IKeep base s w := ku.trans (kv.ikeep.trans (counter_keep wg wm wr ww))
    have bw : BoundedEnv w.mem base := wm ▸ bv
    have ew : E w.mem base = Function.update (E s.mem base) o (Proof.X448.sqn (E s.mem base o) (n - m)) := by
      rw [wm, ev, eu, opMul_update, ← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

end VG.Proof.X448.Arm
