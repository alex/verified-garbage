import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Step

/-!
# A bitsliced round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
(scratch slot `keySlot`) into `r15`, advances the pointer by the step
(`stepSlot`), and does to the 64 state words what `roundW` does, with the
key's low 48 bits.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr)

/-! ## The round key -/

theorem keyLoad_ok {s : State} (h : Room s) (hkey : InRegions (s.rd ++ s.wr) (sl s keySlot) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .r15 = (s.mem.readW (sl s keySlot) 64).rotateRight 48 ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot ∧
      (∀ x < 128, x ≠ keySlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let kp := sl s keySlot
  let K := s.mem.readW kp 64
  let δ := sl s stepSlot
  let s₁ := s.setReg .rax kp
  have e₁ : exec (ld .rax keySlot) s = some s₁ := exec_ld h (by decide) .rax
  let s₂ := s₁.setReg .r15 K
  have e₂ : exec (.mov .r15 (.mem { base := .rax, disp := 0 })) s₁ = some s₂ := by
    have hea : s₁.ea { base := .rax, disp := 0 } = kp := by
      simp [State.ea, s₁, gpr_setReg]
    have hl : s₁.load64 kp = some K := by
      simp only [State.load64, s₁, rd_setReg, wr_setReg, mem_setReg, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  have h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg])
  have sl₂ : ∀ x, sl s₂ x = sl s x := by
    intro x; simp only [sl, s₂, s₁, mem_setReg, gpr_setReg]; rfl
  let s₃ := s₂.setReg .rdx δ
  have e₃ : exec (ld .rdx stepSlot) s₂ = some s₃ := by
    rw [exec_ld h₂ (by decide) .rdx, sl₂]
  let v := kp + δ
  let s₄ := (arithFlags s₃ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .rax v
  have e₄ : exec (.alu .add .rax (.reg .rdx)) s₃ = some s₄ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    have ha : s₃.gpr .rax = kp := by simp [s₃, s₂, s₁, gpr_setReg]
    have hd : s₃.gpr .rdx = δ := by simp [s₃, gpr_setReg]
    rw [ha, hd]
  have h₄ : Room s₄ := h₂.congr (by simp [s₄, s₃, s₂, s₁, gpr_setReg])
    (by simp [s₄, s₃, wr_setReg, wr_arithFlags])
  have e₅ := exec_st (r := Reg.rax) h₄ (by decide : keySlot < 128)
  let s₅ : State := { s₄ with mem := stMem s₄ keySlot (s₄.gpr .rax) }
  let s₆ := (s₅.setFlags (some ((s₅.gpr .r15).rotateRight 48).msb) none s₅.zf s₅.sf).setReg .r15
    ((s₅.gpr .r15).rotateRight 48)
  have e₆ : exec (.shift .ror .r15 48) s₅ = some s₆ := by
    simp only [exec, execShift]; rfl
  have rcx₄ : s₄.gpr .rcx = s.gpr .rcx := by simp [s₄, s₃, s₂, s₁, gpr_setReg]
  have mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rax₄ : s₄.gpr .rax = v := by simp [s₄, gpr_setReg]
  have sl₆ : ∀ x < 128, sl s₆ x = if x = keySlot then v else sl s x := by
    intro x hx
    simp only [sl, s₆, mem_setReg, mem_setFlags, gpr_setReg, gpr_setFlags]
    simp only [show ¬ Reg.rcx = Reg.r15 by decide, ite_false, s₅]
    rw [readW_stMem s₄ (by decide) _ hx, rax₄]
    simp only [sl, mem₄, rcx₄]
  refine ⟨s₆, ?_, ?_, ?_, fun x hx hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_nil]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, K, kp]
  · rw [sl₆ _ (by decide)]; simp; rfl
  · rw [sl₆ x hx]; simp [hne]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, gpr_setFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, gpr_setFlags]
  · have f := stMem_frame (s := s₄) (by decide : keySlot < 128) (s₄.gpr .rax)
    rw [show scratchR s₄ = scratchR s by simp only [scratchR, rcx₄], mem₄] at f
    simpa [s₆, s₅, mem_setReg, mem_setFlags] using f

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
    (hr : s.gpr .r15 = K.rotateRight 48) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .r15 = K.rotateRight 48 <<< (6 * n) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ _ => rfl, by simp [hr], rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, hi₁, r₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := ih (by omega)
    have h₁ := h.congr c₁ wr₁
    obtain ⟨s₂, run₂, w₂, hi₂, r₂, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      sboxStep_ok ρ (by omega : n < 8) h₁ (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact keyBits K (by omega) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      c₂.trans c₁, sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [hi₂ x hx hl, hi₁ x hx hl]
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega]
    · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (ρ : Role) : round ρ = keyLoad ++ stepsCode ρ 8 := rfl

theorem round_ok (ρ : Role) {s : State} (h : Room s)
    (hkey : InRegions (s.rd ++ s.wr) (sl s keySlot) 8) :
    ∃ s', runBlock isa (round ρ) s = some s' ∧
      (∀ x < 64, words s' x =
        roundW ρ ((s.mem.readW (sl s keySlot) 64).setWidth 48) (words s) x) ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, key₁, sl₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := keyLoad_ok h hkey
  have h₁ := h.congr c₁ wr₁
  obtain ⟨s₂, run₂, w₂, hi₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ := stepsCode_ok ρ _ (Nat.le_refl 8) h₁ r₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun x hx hl hne => ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    c₂.trans c₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact steps_congr ρ _ (Nat.le_refl 8)
      (fun y hy => sl₁ _ (by unfold stSlot; omega) (by unfold stSlot keySlot; omega)) x hx
  · rw [hi₂ _ (by decide) (by decide), key₁]
  · rw [hi₂ x hx hl, sl₁ x hx hne]
  · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
    exact f₁.trans f₂

end VG.Proof.TripleDes.X86_64.Bitsliced
