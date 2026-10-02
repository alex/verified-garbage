import VerifiedGarbage.Proof.X25519.X86.Step

/-!
# X25519 on x86 (32-bit): the inversion

The inversion is a sequence of blocks of operations and runs of squarings
(`sqn`, a loop counted by `esi`); each leaves the slots with the values of an
evaluation of it (`runI`), which for the inversion's steps is `invert` of `Z2`
in `T1`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- `n` squarings in place. -/
theorem sqn_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (hb : Base x k s₀ s) {o n : Nat}
    (ho : isSlot 288 o = true) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) :
    WP isa (Impl.X25519.X86.sqn o n) s fun s' => Base x k s₀ s' ∧
      ∀ q, isSlot 288 q = true → F s'.mem x q = Function.update (F s.mem x) o
        (Proof.X25519.sqn (F s.mem x o) n) q := by
  have hv : opValid 288 (.mul o o o) = true := by
    simp only [opValid, opOut, opIns, ho, List.all_cons, List.all_nil, Bool.and_self]
  refine WP.seq (Wp.wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : Base x k s₀ s₁ := hb.of_frame (o := 288) (n := 640) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  refine WP.loop (M := isa) (fun c s' => 1 ≤ c ∧ c ≤ n ∧ Base x k s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 c ∧
      ∀ q, isSlot 288 q = true → F s'.mem x q = Function.update (F s.mem x) o
        (Proof.X25519.sqn (F s.mem x o) (n - c)) q) (fun c s' hc => ?_) n s₁
    ⟨hn, Nat.le_refl _, b₁, u₁.gpr, fun q hq => by
      rw [Nat.sub_self, u₁.mem]
      by_cases e : q = o
      · subst e; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne e]⟩
  obtain ⟨c1, cn, b, esi, hv'⟩ := hc
  refine WP.block_append (WP.mono (op_ok b.ctx (.mul o o o) hv) fun s₂ ⟨k₂, f₂, e₂⟩ => ?_)
  refine Wp.wp_subi fun s₃ u₃ _ z₃ => WP.block_nil ?_
  have b₃ : Base x k s₀ s₃ := (b.ops k₂ f₂).of_frame (o := 288) (n := 640) (u₃.other _ (by decide))
    (u₃.other _ (by decide)) u₃.rd u₃.wr (by rw [u₃.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 (c - 1) := by
    rw [u₃.gpr, k₂.esi, esi]; exact Wp.ofNat_pred c1
  have val₃ : ∀ q, isSlot 288 q = true → F s₃.mem x q = Function.update (F s.mem x) o
      (Proof.X25519.sqn (F s.mem x o) (n - (c - 1))) q := fun q hq => by
    rw [u₃.mem, e₂ q hq]
    simp only [opOut, opVal]
    by_cases e : q = o
    · subst e
      rw [Function.update_self, Function.update_self, hv' q hq, Function.update_self,
        show n - (c - 1) = n - c + 1 by omega_using [c1, cn]]
      rfl
    · rw [Function.update_of_ne e, Function.update_of_ne e, hv' q hq, Function.update_of_ne e]
  have ev : isa.eval .ne s₃ = some (!decide (c - 1 = 0)) := by
    show s₃.zf.map (!·) = _
    rw [z₃, k₂.esi, esi, Wp.ofNat_pred c1, Wp.ofNat_beq_zero (by omega_using [cn, hn'])]; rfl
  by_cases e : c = 1
  · subst e
    refine .inl ⟨by rw [ev]; rfl, b₃, fun q hq => ?_⟩
    rw [val₃ q hq]; rfl
  · exact .inr ⟨by rw [ev]; simp only [show c - 1 ≠ 0 by omega_using [c1, e], decide_false]; rfl, c - 1,
      by omega_using [c1], by omega_using [c1, e], by omega_using [cn], b₃, esi₃, val₃⟩

/-- A step of the inversion: a block of operations, or a run of squarings. -/
inductive IStep
  | ops (l : List Op)
  | sqn (o n : Nat)

def IStep.prog : IStep → Prog isa
  | .ops l => .block (Impl.X25519.X86.ops l)
  | .sqn o n => Impl.X25519.X86.sqn o n

/-- Steps in sequence. -/
def progOf : List IStep → Prog isa
  | [] => .block []
  | [st] => st.prog
  | st :: l => .seq st.prog (progOf l)

def IStep.valid : IStep → Bool
  | .ops l => l.all (opValid 288)
  | .sqn o n => isSlot 288 o && 1 ≤ n && n < 2 ^ 32

/-- The values of the slots after a step. -/
def IStep.run (V : Nat → Fe) : IStep → Nat → Fe
  | .ops l => X86.run l V
  | .sqn o n => Function.update V o (Proof.X25519.sqn (V o) n)

def runI : List IStep → (Nat → Fe) → Nat → Fe
  | [], V => V
  | st :: l, V => runI l (st.run V)

theorem IStep.run_congr {V V' : Nat → Fe} (st : IStep) (hv : st.valid = true)
    (h : ∀ q, isSlot 288 q = true → V q = V' q) : ∀ q, isSlot 288 q = true → st.run V q = st.run V' q := by
  cases st with
  | ops l =>
    simp only [IStep.valid, List.all_eq_true] at hv
    exact X86.run_congr l hv h
  | sqn o n =>
    simp only [IStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro q hq
    by_cases e : q = o
    · subst e; simp only [IStep.run, Function.update_self, h q hq]
    · simp only [IStep.run, Function.update_of_ne e, h q hq]

theorem runI_congr (l : List IStep) (hv : ∀ st ∈ l, st.valid = true) :
    ∀ {V V' : Nat → Fe}, (∀ q, isSlot 288 q = true → V q = V' q) → ∀ q, isSlot 288 q = true → runI l V q = runI l V' q := by
  induction l with
  | nil => exact fun h q hq => h q hq
  | cons st l ih =>
    intro V V' h q hq
    exact ih (fun o ho => hv o (List.mem_cons_of_mem _ ho))
      (IStep.run_congr st (hv st List.mem_cons_self) h) q hq

theorem IStep.ok {x : BitVec 32} {k : Nat} {s₀ s : State} (hb : Base x k s₀ s) (st : IStep)
    (hv : st.valid = true) :
    WP isa st.prog s fun s' => Base x k s₀ s' ∧ ∀ q, isSlot 288 q = true → F s'.mem x q = st.run (F s.mem x) q := by
  cases st with
  | ops l =>
    simp only [IStep.valid, List.all_eq_true] at hv
    exact WP.mono (ops_ok l hb.ctx hv) fun s' ⟨k', f', e'⟩ => ⟨hb.ops k' f', e'⟩
  | sqn o n =>
    simp only [IStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sqn_ok hb hv.1.1 hv.1.2 hv.2

theorem progOf_ok {x : BitVec 32} {k : Nat} {s₀ : State} :
    ∀ (l : List IStep) {s : State}, Base x k s₀ s → (∀ st ∈ l, st.valid = true) →
    WP isa (progOf l) s fun s' => Base x k s₀ s' ∧ ∀ q, isSlot 288 q = true → F s'.mem x q = runI l (F s.mem x) q
  | [], _, hb, _ => WP.block_nil ⟨hb, fun _ _ => rfl⟩
  | [st], _, hb, hv => WP.mono (IStep.ok hb st (hv st List.mem_cons_self)) fun _ ⟨b, e⟩ => ⟨b, e⟩
  | st :: st' :: l, s, hb, hv => by
    refine WP.seq (WP.mono (IStep.ok hb st (hv st List.mem_cons_self)) fun s₁ ⟨b₁, e₁⟩ => ?_)
    refine WP.mono (progOf_ok (st' :: l) b₁ fun o ho => hv o (List.mem_cons_of_mem _ ho))
      fun s₂ ⟨b₂, e₂⟩ => ⟨b₂, fun q hq => ?_⟩
    rw [e₂ q hq]
    exact runI_congr (st' :: l) (fun o ho => hv o (List.mem_cons_of_mem _ ho)) e₁ q hq

/-- The inversion's steps. -/
def invSteps : List IStep :=
  [.ops [.mul T0 Z2 Z2, .copy T1 T0], .sqn T1 2,
    .ops [.mul T1 Z2 T1, .mul T0 T0 T1, .mul T2 T0 T0, .mul T1 T1 T2, .copy T2 T1], .sqn T2 5,
    .ops [.mul T1 T2 T1, .copy T2 T1], .sqn T2 10,
    .ops [.mul T2 T2 T1, .copy T3 T2], .sqn T3 20,
    .ops [.mul T2 T3 T2], .sqn T2 10,
    .ops [.mul T1 T2 T1, .copy T2 T1], .sqn T2 50,
    .ops [.mul T2 T2 T1, .copy T3 T2], .sqn T3 100,
    .ops [.mul T2 T3 T2], .sqn T2 50,
    .ops [.mul T1 T2 T1], .sqn T1 5,
    .ops [.mul T1 T1 T0]]

theorem invert_eq : Impl.X25519.X86.invert = progOf invSteps := rfl

theorem invSteps_valid : ∀ st ∈ invSteps, st.valid = true := by decide

theorem runI_invert (V : Nat → Fe) : runI invSteps V T1 = VG.Proof.X25519.invert (V Z2) := by
  simp only [runI, invSteps, IStep.run, X86.run, opOut, opVal, Function.update_apply, T0, T1, T2, T3, Z2]
  simp (config := {decide := true}) only [ite_true, ite_false]
  rfl

end VG.Proof.X25519.X86
