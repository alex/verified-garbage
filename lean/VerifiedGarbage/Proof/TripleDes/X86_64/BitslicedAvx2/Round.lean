import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Step

/-!
# An AVX2 round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`r8` into `rax`, advances the pointer by the step `r9`, and does to the 64
state words what `roundW` does, with the key's low 48 bits.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx2
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr)

/-! ## The round key -/

theorem keyLoad_ok {s : State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .rax = (s.mem.readW (s.gpr .r8) 64).rotateRight 48 ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧ (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ y, s'.ymm y = s.ymm y) := by
  let kp := s.gpr .r8
  let K := s.mem.readW kp 64
  let δ := s.gpr .r9
  let s₁ := s.setReg .rax K
  have e₁ : exec (.mov .rax (.mem { base := .r8, disp := 0 })) s = some s₁ := by
    have hea : s.ea { base := .r8, disp := 0 } = kp := by simp [State.ea, kp]
    have hl : s.load64 kp = some K := by simp only [State.load64, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  let v := kp + δ
  let s₂ := (arithFlags s₁ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .r8 v
  have e₂ : exec (.alu .add .r8 (.reg .r9)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    have ha : s₁.gpr .r8 = kp := by simp [s₁, gpr_setReg, kp]
    have hd : s₁.gpr .r9 = δ := by simp [s₁, gpr_setReg, δ]
    rw [ha, hd]
  let s₃ := (s₂.setFlags (some ((s₂.gpr .rax).rotateRight 48).msb) none s₂.zf s₂.sf).setReg .rax
    ((s₂.gpr .rax).rotateRight 48)
  have e₃ : exec (.shift .ror .rax 48) s₂ = some s₃ := by
    simp only [exec, execShift]; rfl
  refine ⟨s₃, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, fun y => rfl⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, K, kp]
  · simp [s₃, s₂, gpr_setReg, gpr_setFlags, v, kp, δ]
  · simp [s₃, s₂, s₁, gpr_setReg, gpr_setFlags, h1, h2]
  · simp [s₃, s₂, s₁, mem_setReg, mem_setFlags, mem_arithFlags]
  · simp [s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- S-box `j`'s key bits are at the top of the rotated key, shifted by the
bits of the S-boxes before it. -/
theorem keyBits (K : BitVec 64) {j i : Nat} (hj : j < 8) (hi : i < 6) :
    (K.rotateRight 48 <<< (6 * j)).getLsbD (58 + i) = (K.setWidth 48).getLsbD (inBit j i) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth]
  have h1 : ¬ 58 + i < 6 * j := by omega
  have h2 : ¬ 58 + i - 6 * j < 64 - 48 % 64 := by omega
  have h3 : 58 + i - 6 * j - (64 - 48 % 64) = inBit j i := by unfold inBit; omega
  have h4 : inBit j i < 48 := by unfold inBit; omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and, h2, ite_false, h3, h4, decide_true,
    Bool.true_and, show 58 + i < 64 by omega, show 58 + i - 6 * j < 64 by omega]

theorem stepsCode_ok (ρ : Role) (K : BitVec 64) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hones : s.ymm ones = BitVec.allOnes 256) (hr : s.gpr .rax = K.rotateRight 48) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      s'.gpr .rax = K.rotateRight 48 <<< (6 * n) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.ymm ones = s.ymm ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, by simp [hr], fun _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, r₁, g₁, o₁, rd₁, wr₁, f₁⟩ := ih (by omega)
    have c₁ := g₁ .rcx (by decide) (by decide)
    have si₁ := g₁ .rsi (by decide) (by decide)
    have h₁ := h.congr c₁ si₁ wr₁
    obtain ⟨s₂, run₂, w₂, r₂, g₂, o₂, rd₂, wr₂, f₂⟩ :=
      sboxStep_ok ρ (by omega : n < 8) h₁ (by rw [o₁, hones]) (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact keyBits K (by omega) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      o₂.trans o₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega]
    · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
        show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (ρ : Role) : round ρ = keyLoad ++ stepsCode ρ 8 := rfl

theorem round_ok (ρ : Role) {s : State} (h : Room s) (hones : s.ymm ones = BitVec.allOnes 256)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa (round ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (words s) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.ymm ones = s.ymm ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, k₁, g₁, m₁, rd₁, wr₁, y₁⟩ := keyLoad_ok hkey
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  obtain ⟨s₂, run₂, w₂, -, g₂, o₂, rd₂, wr₂, f₂⟩ :=
    stepsCode_ok ρ _ (Nat.le_refl 8) h₁ (by rw [y₁, hones]) r₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 h3 => ?_, by rw [o₂, y₁], rd₂.trans rd₁,
    wr₂.trans wr₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    have e : ∀ y, words s₁ y = words s y := fun y => by simp only [words, m₁, si₁]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [g₂ _ (by decide) (by decide), k₁]
  · rw [g₂ r h1 h2, g₁ r h1 h3]
  · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
      show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
    rw [m₁] at f₂
    exact f₂

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
