import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Step

/-!
# An AdvSIMD round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`x5`, broadcasts it, steps the pointer by 8 in the pass's direction, and
does to the 64 state words what `roundW` does, with the key's low 48 bits.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ step_congr steps_congr)

/-- The key pointer after a round. -/
def nextKey (d : Direction) (p : Addr) : Addr := if d = .encrypt then p + 8 else p - 8

theorem keyLoad_ok (d : Direction) {s : State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧
      s'.v keyReg = ofVDwords (s.mem.readW (s.gpr .x5) 64) (s.mem.readW (s.gpr .x5) 64) ∧
      s'.gpr .x5 = nextKey d (s.gpr .x5) ∧
      (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ y, y ≠ keyReg → s'.v y = s.v y) := by
  let K := s.mem.readW (s.gpr .x5) 64
  have hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 8 := by
    simpa using hkey
  let s₁ := s.write .x .x9 K
  have e₁ : exec (.ldr .x .x9 .x5 0) s = some s₁ := by
    rw [exec_ldr_x ⟨by decide, by decide⟩ hk0]; simp [s₁, K]
  let s₂ := s₁.setV keyReg (ofVDwords (s₁.gpr .x9) (s₁.gpr .x9))
  have e₂ : exec (.vop (.dup .d2 keyReg .x9)) s₁ = some s₂ := rfl
  have x9₁ : s₁.gpr .x9 = K := by simp [s₁, State.write]
  have x5₂ : s₂.gpr .x5 = s.gpr .x5 := by simp [s₂, s₁, State.write, State.setV]
  let s₃ := s₂.write .x .x5 (nextKey d (s.gpr .x5))
  have e₃ : exec (if d = .encrypt then .addImm .x .x5 .x5 8 else .subImm .x .x5 .x5 8) s₂ =
      some s₃ := by
    cases d
    · simp only [ite_true, exec_addImm_x (show 8 < 4096 by decide)]
      simp only [s₃, nextKey, ite_true, State.read, BitVec.setWidth_eq, x5₂]; rfl
    · simp only [reduceCtorEq, ite_false, exec_subImm_x (show 8 < 4096 by decide)]
      simp only [s₃, nextKey, State.read, BitVec.setWidth_eq, x5₂, reduceCtorEq, ite_false]; rfl
  refine ⟨s₃, ?_, ?_, by simp [s₃, State.write], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_nil]
  · show s₂.v keyReg = _; rw [v_setV_self, x9₁]
  · simp [s₃, s₂, s₁, State.write, State.setV, h1, h2]
  · show s₂.v y = s.v y; rw [v_setV_of_ne _ _ hy]; rfl

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) {K : BitVec 64} {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hk : KeyRegs K s) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, hk, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega)
    have h₁ := room_congr h (by rw [g₁]) wr₁
    obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := sboxStep_ok ρ (by omega : n < 8) h₁ k₁
    refine ⟨s₂, ?_, fun x hx => ?_, k₂, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [show stateR s₁ = stateR s by simp only [stateR, g₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) (hz : s.v zeroReg = 0)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW (s.gpr .x5) 64).setWidth 48) (words s) x) ∧
      s'.gpr .x5 = nextKey d (s.gpr .x5) ∧ (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.v zeroReg = 0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, x5₁, g₁, m₁, rd₁, wr₁, sp₁, v₁⟩ := keyLoad_ok d hkey
  have h₁ := room_congr h (g₁ _ (by decide) (by decide)) wr₁
  have kr : KeyRegs (s.mem.readW (s.gpr .x5) 64) s₁ := ⟨k₁, by rw [v₁ _ (by decide), hz]⟩
  obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := stepsCode_ok ρ (Nat.le_refl 8) h₁ kr
  refine ⟨s₂, ?_, fun x hx => ?_, by rw [g₂, x5₁], fun r h1 h2 => by rw [g₂, g₁ r h1 h2], k₂.zero,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    have e : ∀ y, words s₁ y = words s y := fun y => by
      simp only [words, m₁, g₁ .x4 (by decide) (by decide)]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [show stateR s₁ = stateR s by simp only [stateR, g₁ .x4 (by decide) (by decide)], m₁] at f₂
    exact f₂

end VG.Proof.TripleDes.AArch64.BitslicedNeon
