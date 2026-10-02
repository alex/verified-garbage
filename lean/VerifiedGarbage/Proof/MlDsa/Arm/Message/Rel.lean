import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `r7`, which they keep, leak the same in runs that agree on it
(`block_r7_tr`): the moves of a call's arguments are such (`setArgs_r7`).
Two runs with the same layout, each in `Ctx` with inputs related by `I`
(`Two`), and the moves of a call's arguments in them (`setArgs_two`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-! ## Blocks addressed from `r7` -/

/-- An instruction whose addresses are a function of `r7`, which it keeps. -/
def R7Only (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .r7 = s₂.gpr .r7 → isa.addrs i s₁ = isa.addrs i s₂) ∧ dstOf i ≠ some .r7

theorem execBlock_r7_tr : ∀ {is : List Instr}, (∀ i ∈ is, R7Only i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .r7 = s₂.gpr .r7 →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h7, e₁, e₂ => by
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    rename_i a₁ ha₁
    split at e₂ <;> [cases e₂; skip]
    rename_i a₂ ha₂
    obtain ⟨⟨b₁, u₁⟩, eb₁, he₁⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨⟨b₂, u₂⟩, eb₂, he₂⟩ := Option.map_eq_some_iff.mp e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    have hi := h i (List.mem_cons_self ..)
    have h7' : a₁.gpr .r7 = a₂.gpr .r7 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h7]
    have ht := execBlock_r7_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h7' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h7, ht]

theorem block_r7_tr {is : List Instr} (h : ∀ i ∈ is, R7Only i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .r7 = b.gpr .r7) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_r7_tr h (hp _ _ hP) e₁ e₂, trivial⟩

theorem arg_r7 (d : Reg) (hd : d ≠ .r7) (a : Arg) : ∀ i ∈ a.mov d, R7Only i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    (try rcases hi with rfl | rfl) <;> (try subst hi) <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, h], by simpa [dstOf] using hd⟩

theorem setArgs_r7 {as : List (Reg × Arg)} (h : argsOk as = true) : ∀ i ∈ setArgs as, R7Only i := by
  induction as with
  | nil => intro i hi; simp [setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact arg_r7 d h.1.1.2 a i hi
    · exact ih h.2 i hi

/-- A relation proved through the final states' facts, from those of each run. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-! ## Runs related through their entry states -/

/-- Two runs whose states are related to entry states `x`, `y` by `A`, with
`P x y`. -/
def Ghost (P A : State → State → Prop) (a b : State) : Prop := ∃ x y, P x y ∧ A x a ∧ A y b

/-- What each run satisfies by correctness, from its entry state, carries over. -/
theorem ghost_step {P A B : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (Ghost P A) c (Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-- Code the taint analysis proves constant time from the registers `rs`
and the first `n` bytes of stack arguments, on which runs related by `R`
agree. -/
theorem argRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg) (n : Nat)
    (hr : ∀ x y, R x y → VG.Arm.Taint.Agree (argTaint rs n) x y) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (argTaint rs n) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (argTaint rs n) hr h

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, R x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hr a b hab)) h

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.r7 {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) :
    a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.r7.trans c₂.r7.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ Only (as.map (·.1)) t t1

/-- The moves of a call's arguments in two runs. -/
theorem setArgs_two {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) :
    RelCT isa (Two I Φ) (.block (setArgs as)) fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1 :=
  RelCT.postDep (block_r7_tr (setArgs_r7 hok) fun _ _ h => h.r7.1)
    (fun x y ⟨_, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x (c₁.xOk hL), setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y _ _ hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩

end

end VG.Proof.MlDsa.Arm.Message
