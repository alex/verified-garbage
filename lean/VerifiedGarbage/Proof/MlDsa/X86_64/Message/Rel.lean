import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Entry
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: relating two runs

Untrusted: everything here is checked by Lean. Two runs between the frame's
push and pop with the same layout, each in a `Ctx` state, whose inputs agree
on what the contract makes public (`I`), and each satisfying `Φ` (`Two`).
Blocks whose addresses are `rsp` plus offsets leak the same in both runs
(`block_rsp_tr`, and so the moves of a call's arguments, `setArgs_tr`); a
call whose callee's public data agree in both runs (`call_tr`); and what
each run satisfies by correctness carries over (`two_wp`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)

/-! ## Blocks addressed from `rsp` -/

/-- An instruction whose addresses are a function of `rsp`, which it keeps. -/
def SpOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .rsp = s₂.gpr .rsp → isa.addrs i s₁ = isa.addrs i s₂) ∧ Taint.clobbers i .rsp = false

theorem execBlock_rsp_tr : ∀ {is : List Instr}, (∀ i ∈ is, SpOnly i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .rsp = s₂.gpr .rsp →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
      t₁ = t₂ ∧ s₁'.gpr .rsp = s₂'.gpr .rsp
  | [], _, _, _, _, _, _, _, hsp, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂
    exact ⟨rfl, hsp⟩
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, hsp, e₁, e₂ => by
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
    have hsp' : a₁.gpr .rsp = a₂.gpr .rsp := by
      rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, hsp]
    obtain ⟨ht, hs⟩ := execBlock_rsp_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) hsp' eb₁ eb₂
    exact ⟨by rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ hsp, ht], hs⟩

theorem block_rsp_tr {is : List Instr} (h : ∀ i ∈ is, SpOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .rsp = b.gpr .rsp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_rsp_tr h (hp _ _ hP) e₁ e₂).1, trivial⟩

theorem arg_spOnly (d : Reg) (hd : d ≠ .rsp) (a : Arg) : ∀ i ∈ a.mov d, SpOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h],
      by cases d <;> simp_all [Taint.clobbers, Taint.dstOf]⟩

theorem setArgs_spOnly (as : List Arg) : ∀ i ∈ setArgs as, SpOnly i := by
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  have hd : d ∈ argRegs6 := (List.of_mem_zip hm).1
  exact arg_spOnly d (fun e => by subst e; revert hd; decide) a i hi

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

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 64) (mx₁ mx₂ : BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ mx₁ m₁ a ∧ Ctx L g₂ mx₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.rsp {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) : a.gpr .rsp = b.gpr .rsp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h; c₁.rsp.trans c₂.rsp.symm

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : Two I Φ a b) : Two I Ψ a b :=
  let ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List Arg) (t t1 : State) : Prop :=
  (ArgsIn as t t1 ∧ t1.mem = t.mem ∧ t1.mxcsr = t.mxcsr) ∧ Keep argRegs t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List Arg} (hok : as.all Arg.ok = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t t1 : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t → Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ mx₁ mx₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ mx₁ m₁ a →
      Ctx L g₂ mx₂ m₂ b → Φ L m₁ a → Φ L m₂ b → Moved as a a1 → Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.wr, Within r R)) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1)
    (block_rsp_tr (setArgs_spOnly as) fun _ _ h => h.rsp)
    (fun x y ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x c₁.frOk, setArgs_ok as hok y c₂.frOk⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  refine RelCT.callEx hv hct fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_
  obtain ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ mx₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g mx m₀}, Ctx L g mx m₀ t → Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.2.1, f.2.2.2, hc.rd, hc.wr]
    refine ⟨covers_of_within fun r hr' => ?_, covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, by simp [hR], hW⟩
    · obtain ⟨R, hR, hW⟩ := hw r hr'
      exact ⟨R, List.mem_cons_of_mem _ hR, hW⟩
  exact ⟨rd L, wr L, rd L, wr L, hpre L g₁ mx₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ mx₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2,
    by rw [f₁.2.gpr (by decide), f₂.2.gpr (by decide), c₁.rsp, c₂.rsp]⟩

end

end VG.Proof.MlDsa.X86_64.Message
