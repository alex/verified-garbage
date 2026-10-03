import VerifiedGarbage.Proof.Rc4.AArch64.WriteJ

/-!
# One swap

`swapStep_run`: with the table `R` in the table registers (indexed from the
base), `j` (from the base) broadcast in `v0` and `S[i] = R l` broadcast in
`v4`, the swap step adds `R l` to `j`, swaps `R l` and `R j`, leaves the
next `S[i]` (the new `R (l + 1)`) in `v4` and, in the PRGA, the output index
`R l + R j - B` in `v6`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem dupE_bc (s : State) (n : VReg) (i : Nat) :
    VArr.b16.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0 = bc (vbyte (s.v n) i) :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, vbyte_bc _ he]
    rfl

/-- What follows the write at `j`: the output index, in the PRGA, the next
`S[i]`, and the write at `i`. -/
def stepTail (prga : Bool) (l : Nat) : List Instr :=
  (if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) ++
  [.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16)), .vop (.insE .b16 (treg 0) l .v5 0)]

theorem swapStep_eq (prga : Bool) (l : Nat) :
    swapStep prga l = ([.vop (.add .b16 (dq 0) (dq 0) si)] : List Instr) ++
      (quarters (dq 0) (dq 1) (dq 2) (dq 3) ++ (lookup .v5 .v6 (dq 0) (dq 1) (dq 2) (dq 3) ++
        (writeN 16 ++ stepTail prga l))) := by
  simp only [swapStep, stepTail, writeJ, writeN, List.append_assoc]

/-- The registers a swap step changes. -/
def stepRegs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
   .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- The table after the swap of positions `l` and `J`. -/
def swapR (R : Nat → BitVec 8) (l J : Nat) (k : Nat) : BitVec 8 :=
  if k = l then R J else if k = J then R l else R k

theorem consts_of_only {s s' : State} (hk : Consts s) (h : Only stepRegs s s') : Consts s' :=
  hk.congr fun r hr => h.2 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem swapStep_run (prga : Bool) {l : Nat} (hl : l < 16) {s : State} (hk : Consts s)
    {Jr NB : BitVec 8} (hj : s.v (dq 0) = bc Jr) (hi : s.v si = bc (tbyte s.v l))
    (hn : prga = true → s.v negBase = bc NB) :
    ∃ s', runBlock isa (swapStep prga l) s = some s' ∧
      (∀ k < 256, tbyte s'.v k =
        swapR (tbyte s.v) l (Jr + tbyte s.v l).toNat k) ∧
      s'.v (dq 0) = bc (Jr + tbyte s.v l) ∧
      s'.v si = bc (swapR (tbyte s.v) l (Jr + tbyte s.v l).toNat (l + 1)) ∧
      (prga = true → s'.v .v6 = bc (tbyte s.v l + tbyte s.v (Jr + tbyte s.v l).toNat + NB)) ∧
      Only stepRegs s s' := by
  let R := tbyte s.v
  let J := Jr + R l
  -- j += S[i]
  let s₁ := s.setV (dq 0) (VArr.b16.map2 (fun _ x y => x + y) (s.v (dq 0)) (s.v si))
  have e₁ : exec (.vop (.add .b16 (dq 0) (dq 0) si)) s = some s₁ := rfl
  have o₁ : Only stepRegs s s₁ := Only.setV _ (by decide) _
  have j₁ : s₁.v (dq 0) = bc J := by rw [v_setV_self, hj, hi, add_bc]
  have k₁ : Consts s₁ := consts_of_only hk o₁
  have t₁ : tbyte s₁.v = R := by
    funext k; simp only [tbyte, R]; rw [v_setV_of_ne _ _ ((show NotTable (dq 0) by decide).ne _)]
  -- the quarters
  obtain ⟨s₂, run₂, a₂, b₂, c₂, o₂⟩ := quarters_run (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) k₁ J j₁ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have o₂' : Only stepRegs s s₂ := o₁.trans (o₂.mono (by decide))
  have j₂ : s₂.v (dq 0) = bc J := by rw [o₂.2 _ (by decide), j₁]
  have t₂ : tbyte s₂.v = R := by
    rw [← t₁]; funext k; simp only [tbyte]
    rw [o₂.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable (dq 1) by decide).ne _, (show NotTable (dq 2) by decide).ne _,
        (show NotTable (dq 3) by decide).ne _⟩)]
  -- S[j]
  obtain ⟨s₃, run₃, v₃, o₃⟩ := lookup_run (d := .v5) (t := .v6) (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) J j₂ a₂ b₂ c₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have o₃' : Only stepRegs s s₃ := o₂'.trans (o₃.mono (by decide))
  have t₃ : tbyte s₃.v = R := by
    rw [← t₂]; funext k; simp only [tbyte]
    rw [o₃.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v5 by decide).ne _, (show NotTable .v6 by decide).ne _⟩)]
  have v₃' : s₃.v .v5 = bc (R J.toNat) := by rw [v₃, t₂]
  -- S[j] := S[i]
  have q₃ : Quarters s₃ J := by
    intro q hq
    rw [o₃.2 _ (by revert q; decide)]
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
    · rw [j₂, show J ^^^ BitVec.ofNat 8 (64 * 0) = J from BitVec.xor_zero]
    · exact a₂
    · exact b₂
    · exact c₂
  have i₃ : s₃.v si = bc (R l) := by
    rw [o₃.2 _ (by decide), o₂.2 _ (by decide), v_setV_of_ne _ _ (by decide), hi]
  obtain ⟨s₄, run₄, t₄, o₄⟩ := writeN_run (consts_of_only hk o₃') q₃ i₃ (Nat.le_refl 16)
  have o₄' : Only stepRegs s s₄ := o₃'.trans (o₄.mono (by decide))
  have tb₄ : ∀ k < 256, tbyte s₄.v k = if k = J.toNat then R l else R k := by
    intro k hk
    rw [t₄ k hk, t₃]
    exact ite_iff ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩ _ _
  have five₄ : s₄.v .v5 = bc (R J.toNat) := by rw [o₄.2 _ (by decide), v₃']
  have i₄ : s₄.v si = bc (R l) := by rw [o₄.2 _ (by decide), i₃]
  have j₄ : s₄.v (dq 0) = bc J := by rw [o₄.2 _ (by decide), o₃.2 _ (by decide), j₂]
  have n₄ : prga = true → s₄.v negBase = bc NB := fun h => by
    rw [o₄'.2 _ (by decide)]; exact hn h
  -- the output index
  obtain ⟨s₆, run₆, six₆, o₆⟩ : ∃ s₆, runBlock isa
      ((if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) :
        List Instr) s₄ = some s₆ ∧
      (prga = true → s₆.v .v6 = bc (R l + R J.toNat + NB)) ∧ Only [.v6] s₄ s₆ := by
    cases prga
    · exact ⟨s₄, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil,
        fun h => absurd h (by decide), Only.refl _ _⟩
    · let a := s₄.setV .v6 (VArr.b16.map2 (fun _ x y => x + y) (s₄.v si) (s₄.v .v5))
      let b := a.setV .v6 (VArr.b16.map2 (fun _ x y => x + y) (a.v .v6) (a.v negBase))
      refine ⟨b, ?_, fun _ => ?_, (Only.setV _ (by simp) _).trans (Only.setV _ (by simp) _)⟩
      · have ea : exec (.vop (.add .b16 .v6 si .v5)) s₄ = some a := rfl
        have eb : exec (.vop (.add .b16 .v6 .v6 negBase)) a = some b := rfl
        simp only [ite_true]
        rw [runBlock_cons, ea, runStep_some, runBlock_cons, eb, runStep_some, runBlock_nil]
      · simp only [b, v_setV_self, a, v_setV_of_ne _ _ (show negBase ≠ .v6 by decide), i₄, five₄,
          n₄ rfl, add_bc]
  have t₆ : tbyte s₆.v = tbyte s₄.v := by
    funext k; simp only [tbyte]; rw [o₆.2 _ (by simp [(show NotTable .v6 by decide).ne _])]
  have five₆ : s₆.v .v5 = bc (R J.toNat) := by rw [o₆.2 _ (by decide), five₄]
  have j₆ : s₆.v (dq 0) = bc J := by rw [o₆.2 _ (by decide), j₄]
  -- the next S[i]
  let s₇ := s₆.setV si (VArr.b16.map2 (fun w _ _ => (s₆.v (treg ((l + 1) / 16))).extractLsb'
    (w * ((l + 1) % 16)) w) 0 0)
  have e₇ : exec (.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16))) s₆ = some s₇ := by
    rw [exec_vop']
    simp only [VOp.eval, VArr.esize, show (l + 1) % 16 < 128 / 8 by omega, ite_true]
    rfl
  have i₇ : s₇.v si = bc (tbyte s₄.v (l + 1)) := by
    rw [v_setV_self, dupE_bc, ← t₆]; rfl
  -- S[i] := S[j]
  let s₈ := s₇.setV (treg 0) (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
  have e₈ : exec (.vop (.insE .b16 (treg 0) l .v5 0)) s₇ = some s₈ := by
    rw [exec_vop']
    simp only [VOp.eval, VArr.esize, show l < 128 / 8 by omega, show 0 < 128 / 8 by omega,
      and_self, ite_true]
    rfl
  have five₇ : s₇.v .v5 = bc (R J.toNat) := by rw [v_setV_of_ne _ _ (by decide), five₆]
  have t₇ : tbyte s₇.v = tbyte s₄.v := by
    rw [← t₆]; funext k; simp only [tbyte]
    rw [v_setV_of_ne _ _ ((show NotTable si by decide).ne _)]
  have tb₈ : ∀ k < 256, tbyte s₈.v k = swapR R l J.toNat k := by
    intro k hk
    by_cases h0 : k / 16 = 0
    · have : tbyte s₈.v k = vbyte (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
          (k % 16) := by simp only [tbyte, h0, s₈, v_setV_self]
      rw [this, vbyte_setLane _ _ hl (by omega), extract_byte, five₇, vbyte_bc _ (by decide)]
      have old : vbyte (s₇.v (treg 0)) (k % 16) = tbyte s₄.v k := by
        rw [← t₇]; simp only [tbyte, h0]
      rw [old, tb₄ k hk, swapR]
      exact ite_iff ⟨fun h => by omega, fun h => by omega⟩ _ _
    · have : tbyte s₈.v k = tbyte s₇.v k := by
        simp only [tbyte, s₈]
        rw [v_setV_of_ne _ _ (fun h => h0 (treg_inj _ (by omega) _ (by decide) h))]
      rw [this, t₇, tb₄ k hk, swapR, ite_eq_right (show ¬ k = l by omega)]
  refine ⟨s₈, ?_, tb₈, ?_, ?_, ?_, ?_⟩
  · rw [swapStep_eq, List.singleton_append, runBlock_cons, e₁, runStep_some]
    refine runBlock_cat_some run₂ (runBlock_cat_some run₃ (runBlock_cat_some run₄
      (runBlock_cat_some run₆ ?_)))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), j₆]
  · rw [v_setV_of_ne _ _ (by decide), i₇, tb₄ _ (by omega), swapR,
      ite_eq_right (show ¬ (l + 1 = l) by omega)]
  · intro hp
    rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), six₆ hp]
  · exact ((o₄'.trans (o₆.mono (by decide))).trans (Only.setV _ (by decide) _)).trans
      (Only.setV _ (by decide) _)

end VG.Proof.Rc4.AArch64
