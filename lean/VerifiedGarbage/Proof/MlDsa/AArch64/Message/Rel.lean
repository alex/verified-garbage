import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `x28` and the stack pointer, which they keep, leak the same in
runs that agree on those (`block_x28_tr`): the moves of a call's arguments
are such (`setArgs_xOnly`). Two runs with the same layout, each in `Ctx`
with inputs related by `I` (`Two`), and a call in them of verified code
whose public data agree (`call_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)

/-! ## Blocks addressed from `x28` -/

/-- An instruction whose addresses are a function of `x28` and the stack
pointer, which it keeps. -/
def XOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp → isa.addrs i s₁ = isa.addrs i s₂) ∧
    dstOf i ≠ some .x28

theorem execBlock_x28_tr : ∀ {is : List Instr}, (∀ i ∈ is, XOnly i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h28, hsp, e₁, e₂ => by
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
    have h28' : a₁.gpr .x28 = a₂.gpr .x28 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h28]
    have hsp' : a₁.sp = a₂.sp := by rw [exec_sp ha₁, exec_sp ha₂, hsp]
    have ht := execBlock_x28_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h28' hsp' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h28 hsp, ht]

theorem block_x28_tr {is : List Instr} (h : ∀ i ∈ is, XOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_x28_tr h (hp _ _ hP).1 (hp _ _ hP).2 e₁ e₂, trivial⟩

theorem arg_xOnly (d : Reg) (hd : d ≠ .x28) (a : Arg) : ∀ i ∈ a.mov d, XOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h _ => by simp [addrs, h], by simpa [dstOf] using hd⟩

theorem setArgs_xOnly {as : List (Reg × Arg)} (h : argsOk as = true) : ∀ i ∈ setArgs as, XOnly i := by
  induction as with
  | nil => intro i hi; simp [setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact arg_xOnly d h.1.1.2 a i hi
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

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.x28 {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) :
    a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.x28.trans c₂.x28.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g v m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ v₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ v₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_mono {Φ Ψ : Lay → Mem → State → Prop} (h : ∀ L m t, Φ L m t → Ψ L m t) {a b : State}
    (hp : Two I Φ a b) : Two I Ψ a b :=
  let ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ Only (as.map (·.1)) t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g v m₀ (t t1 : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t → Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ v₁ m₁ a →
      Ctx L g₂ v₂ m₂ b → Φ L m₁ a → Φ L m₂ b → Moved as a a1 → Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.wr, Within r R)) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1)
    (block_x28_tr (setArgs_xOnly hok) fun _ _ h => h.x28)
    (fun x y ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x (c₁.xOk hL), setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ a b, (∃ (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
      (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧ Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b) ∧
      Moved as a a1 ∧ Moved as b b1)
    (RelCT.exists_ fun L => RelCT.call hv hct (rd L) (wr L) fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_)
    (fun a1 b1 ⟨a, b, ⟨L, hp⟩, f₁, f₂⟩ => ⟨L, a, b, hp, f₁, f₂⟩) fun _ _ h => h
  obtain ⟨g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ v₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g v m₀}, Ctx L g v m₀ t → Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
    refine ⟨covers_of_within fun r hr' => ?_, covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, by simp [hR], hW⟩
    · exact hw r hr'
  exact ⟨hpre L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2⟩

end

end VG.Proof.MlDsa.AArch64.Message
