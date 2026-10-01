import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Public scalar values held in vector registers

Memory remains secret. DUP can preserve a public GPR in a whole vector,
and UMOV recovers a public scalar from a public vector. Other SIMD
operations and vector loads conservatively erase all vector publicity.
-/

namespace VG.AArch64.VectorTaint

instance : RegIdx VReg := ⟨VReg.ctorIdx, fun {a b} h => by
  rw [← VReg.ofNat_ctorIdx a, h, VReg.ofNat_ctorIdx]⟩

abbrev T := Taint.T × RegSet VReg

def ofRegs (rs : List Reg) : T := (Taint.ofRegs rs, RegSet.ofList [])

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  Taint.Agree τ.1 s₁ s₂ ∧ ∀ v ∈ τ.2, s₁.v v = s₂.v v

def setV (τ : RegSet VReg) (v : VReg) (p : Bool) : RegSet VReg :=
  if p then τ.insert v else τ.erase v

/-- Instructions that leave every vector register unchanged. -/
def scalar : Instr → Bool
  | .vop _ | .ldrq .. | .umov .. => false
  | _ => true

def afterV (τ : RegSet VReg) (i : Instr) : RegSet VReg :=
  if scalar i then τ else RegSet.ofList []

def step (τ : T) : Instr → Option T
  | .vop (.dup _ d n) => some (τ.1, setV τ.2 d (Taint.pub τ.1 n))
  | .umov _ d n _ => some (Taint.set τ.1 d (τ.2.mem n), τ.2)
  | i => (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i))

private theorem scalar_vectors {i : Instr} {s s' : State}
    (hi : scalar i = true) (he : exec i s = some s') : s'.v = s.v := by
  cases i <;> simp only [scalar, Bool.false_eq_true] at hi
  all_goals
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  all_goals
    repeat' first
      | split at he
      | simp only [Option.map_eq_some_iff] at he
      | rcases he with ⟨_, _, he⟩
  all_goals
    simp_all only [State.store]
  all_goals
    repeat' first | split at he | cases he
  all_goals rfl

private theorem vectors_set {τ : RegSet VReg} {s₁ s₂ : State}
    (h : ∀ v ∈ τ, s₁.v v = s₂.v v) (d : VReg) {p : Bool} {x₁ x₂ : BitVec 128}
    (hx : p = true → x₁ = x₂) :
    ∀ v ∈ setV τ d p, (s₁.setV d x₁).v v = (s₂.setV d x₂).v v := by
  intro v hv
  unfold setV at hv
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hv
    by_cases hd : v = d
    · simp only [RegUpd.v_setV, hd, ite_true, hx hp]
    · simp only [RegUpd.v_setV, ite_eq_right hd, h v (hv.resolve_left hd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hv
    simp only [RegUpd.v_setV, ite_eq_right hv.1, h v hv.2]

private theorem ordinary_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂)
    (hs : (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i)) = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
  have h := Taint.step_sound ha.1 hg e₁ e₂
  refine ⟨h.1, h.2, ?_⟩
  intro v hv
  unfold afterV at hv
  split at hv
  · rw [scalar_vectors (by assumption) e₁, scalar_vectors (by assumption) e₂]
    exact ha.2 v hv
  · simp only [RegSet.mem_ofList, List.not_mem_nil] at hv

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | vop op =>
    cases op <;> try exact ordinary_sound ha hs e₁ e₂
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      cases a <;> simp only [exec, VOp.eval, Option.map_some, Option.some.injEq] at e₁ e₂
      all_goals
        subst e₁; subst e₂
        refine ⟨rfl, ⟨ha.1.1, ha.1.2⟩, vectors_set ha.2 d ?_⟩
        intro hp; rw [ha.1.reg hp]
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hk
    simp only [hk, ite_true, Option.some.injEq] at e₁ e₂
    subst e₁; subst e₂
    refine ⟨rfl, ha.1.write sz d (fun hp => ?_), fun v hv => ha.2 v hv⟩
    rw [ha.2 n hp]
  | _ =>
    exact ordinary_sound ha hs e₁ e₂

def taint : VG.Taint isa where
  T := T
  Agree := Agree
  step := step
  step_sound := step_sound
  condPub τ := Taint.condPub τ.1
  cond_sound h hc := Taint.cond_sound h.1 hc
  meet τ σ := (τ.1.inter σ.1, τ.2.inter σ.2)
  meet_left h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).1⟩,
    fun v hv => h.2 v (RegSet.mem_inter.mp hv).1⟩
  meet_right h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).2⟩,
    fun v hv => h.2 v (RegSet.mem_inter.mp hv).2⟩
  le τ σ := τ.1.subset σ.1 && τ.2.subset σ.2
  le_sound hl h := by
    simp only [Bool.and_eq_true] at hl
    obtain ⟨hg, hv⟩ := hl
    exact ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_of_subset hg hr)⟩,
      fun v hr => h.2 v (RegSet.mem_of_subset hv hr)⟩
  call τ := (VG.AArch64.taint.call τ.1).map (fun g => (g, τ.2))
  call_sound h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := VG.AArch64.taint.call_sound h.1 hg e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁; subst e₂
    exact ⟨ht.1, ht.2, h.2⟩
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  push τ i := (Taint.push τ.1 i).map (fun g => (g, τ.2))
  push_sound {τ τ' i s₁ s₂ s₁' s₂'} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.push_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.push, reduceCtorEq] at hg
    all_goals
      simp only [isa, push] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩
  pop τ i := (Taint.pop τ.1 i).map (fun g => (g, τ.2))
  pop_sound {τ τ' i a₁ a₂ b₁ b₂ c₁ c₂} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.pop_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.pop, reduceCtorEq] at hg
    all_goals
      simp only [isa, pop] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩

end VG.AArch64.VectorTaint
