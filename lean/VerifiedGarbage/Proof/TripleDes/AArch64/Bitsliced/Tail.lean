import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Ecb

/-!
# The blocks left

Fewer than 128 blocks left (`k` of them, at `x1`) are copied into the
scratch buffer (at `x3`), run there as a batch whose other lanes hold
whatever the buffer held, and copied back (`tail_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)

/-- What the blocks left need: the `k < 128` blocks at `x1` writable, the
scratch buffer at `x3` writable, the schedule at `x0` readable, apart from
each other. -/
structure TailEnv (s : State) (k : Nat) : Prop where
  lt : k < 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 k
  dataW : ∀ i < k, InRegions s.wr (wAt (s.gpr .x1) i) 8
  scratch : (⟨s.gpr .x3, 1024⟩ : Region) ∈ s.wr
  key : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * k⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * k⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩

/-- The registers the blocks left change. -/
def TailRegs (r : Reg) : Prop :=
  r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure TailPost (d : Direction) (k : Nat) (s s' : State) : Prop where
  out : ∀ b < k, blockAt s'.mem (wAt (s.gpr .x1) b) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x1) b))
  gpr : ∀ r, TailRegs r → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr .x1, 8 * k⟩, ⟨s.gpr .x3, 1024⟩] s.mem s'.mem

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

theorem scratch_word {B : Addr} {i : Nat} (hi : i < 128) :
    (⟨B, 1024⟩ : Region).Contains (wAt B i) 8 := Offset.contains_base _ (by omega) (by omega)

theorem tail_ok (d : Direction) {k : Nat} {s : State} (E : TailEnv s k) :
    WP isa (tail d) s (TailPost d k s) := by
  let D := s.gpr .x1
  let B := s.gpr .x3
  let S := s.gpr .x0
  have hk := E.lt
  have scrIn : ∀ i < 128, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, E.scratch, scratch_word hi⟩
  rw [tail]
  apply WP.ite _ (eval_zero s .x2 E.x2 (by omega))
  · intro hz
    have hk0 : k = 0 := by simpa using hz
    subst hk0
    apply WP.block_nil
    exact ⟨fun b hb => by omega, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · intro hnz
    have hk0 : k ≠ 0 := by simpa using hnz
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₁ := ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₁' := s₁.write .x .x13 (s₁.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₁', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have g₁ : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁'.gpr r = s.gpr r := by
      intro r a b c; simp [s₁', s₁, State.write, a, b, c]
    have pre₁ : CopyPre D B k s₁' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
      · obtain ⟨r, hr, hc⟩ := E.dataW i hi
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      · exact scrIn i (by omega)
      · exact E.dataBuf.sub_right (Region.sub_prefix (by omega))
    have inv₁ : CopyInv D B k s₁' 0 s₁' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, D]
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, B]
      · simp [s₁', s₁, State.write, State.read, E.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₁ s₁' 0 inv₁)
    intro s₂ c₂
    have g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s.gpr r :=
      fun r a b c e => (c₂.regs r ⟨a, b, c, e⟩).trans (g₁ r b c e)
    apply WP.seq
    -- x4 := x3
    let s₃ := s₂.write .x .x4 (s₂.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₃, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have g₃ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₃, State.write, a, ite_false]; exact g₂ r b c e f
    have x4₃ : s₃.gpr .x4 = B := by
      simp [s₃, State.write, State.read]; exact g₂ _ (by decide) (by decide) (by decide) (by decide)
    have wr₃ : s₃.wr = s.wr := c₂.wr
    have room₃ : Room s₃ := Ok.of_off (off := 0) (by rw [wr₃]; exact E.scratch)
      (by show s₃.gpr .x4 = _; rw [x4₃]; simp [B]) (by show 0 + 16 * 64 ≤ 1024; decide) (by show 1024 < 2 ^ 64; decide)
    have st₃ : stateR s₃ = ⟨B, 1024⟩ := by simp only [stateR, x4₃]
    have S₃ : Sched s₃ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        show InRegions (s₂.rd ++ s₂.wr) _ 8
        rw [c₂.rd, c₂.wr]; exact E.key i hi
      · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), st₃]; exact E.keyBuf
    apply WP.seq
    apply WP.mono (batch_ok d room₃ S₃)
    intro s₄ q₄
    have g₄ : ∀ r, TailRegs r → s₄.gpr r = s.gpr r := by
      intro r ⟨a, b, c, e, f, i, j, l⟩
      rw [q₄.gpr r b c e f, g₃ r a f i j l]
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₅ := ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₅' := s₅.write .x .x13 (s₅.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₅', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have g₅ : ∀ r, TailRegs r → s₅'.gpr r = s.gpr r := by
      intro r hr
      have ⟨_, _, _, _, _, i, j, l⟩ := hr
      simp only [s₅', s₅, State.write, i, j, l, ite_false]; exact g₄ r hr
    have wr₅ : s₅'.wr = s.wr := q₄.wr.trans wr₃
    have rd₅ : s₅'.rd = s.rd := q₄.rd.trans c₂.rd
    have pre₂ : CopyPre B D k s₅' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega)
        rw [wr₅]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₅]; exact E.dataW i hi
      · exact (E.dataBuf.sub_right (Region.sub_prefix (by omega))).symm
    have inv₂ : CopyInv B D k s₅' 0 s₅' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · simp [s₅', s₅, State.write, State.read]
        rw [g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide⟩, E.x2]
    apply WP.mono (copy_ok pre₂ s₅' 0 inv₂)
    intro s₆ c₆
    -- memory
    have m₃ : s₃.mem = s₂.mem := rfl
    have m₅ : s₅'.mem = s₄.mem := rfl
    have dataSep : (⟨D, 8 * k⟩ : Region).Disjoint ⟨B, 8 * k⟩ :=
      E.dataBuf.sub_right (Region.sub_prefix (by omega))
    have K₃ : scheduleAt s₃.mem (s₃.gpr .x0) = scheduleAt s.mem S := by
      rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), m₃]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S c₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyBuf.sub_right (Region.sub_prefix (by omega))
    refine ⟨fun b hb => ?_, fun r hr => (c₆.regs r ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2⟩).trans (g₅ r hr), c₆.rd.trans rd₅, c₆.wr.trans wr₅,
      c₆.sp.trans (q₄.sp.trans c₂.sp), ?_⟩
    · -- the block in the data, from the scratch buffer after the batch
      have e₆ : blockAt s₆.mem (wAt D b) = blockAt s₄.mem (wAt B b) := by
        rw [← m₅]; exact blockAt_eq_of_readW (c₆.copied b hb)
      -- the block in the scratch buffer before the batch, from the data
      have e₂ : blockAt s₂.mem (wAt B b) = blockAt s.mem (wAt D b) := by
        refine blockAt_eq_of_readW ((c₂.copied b hb).trans ?_)
        rfl
      rw [e₆]
      have o := q₄.out b (by omega)
      rw [x4₃, K₃, m₃, e₂] at o
      exact o
    · have a : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s.mem s₂.mem := c₂.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
      have b : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s₂.mem s₄.mem := q₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [st₃]; exact fun _ h => h⟩
      have c : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s₅'.mem s₆.mem := c₆.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      rw [m₅] at c
      exact (a.trans b).trans c

end VG.Proof.TripleDes.AArch64.BitslicedNeon
