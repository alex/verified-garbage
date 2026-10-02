import VerifiedGarbage.Proof.TripleDes.Arm.Box
import VerifiedGarbage.Proof.TripleDes.Arm.RoundFunction
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  (boxPiece i (Spec.TripleDes.sBox i
    (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 32

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr .r11 = r) (hk : keyWord s = k)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r10 = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .r10) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := box_ok i hi s hok hread
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, keep₁ .r2 (by decide)]
    have hr₁ : s₁.gpr .r11 = r := (keep₁ .r11 (by decide)).trans hr
    have hword (j : Nat) (hj : j < 2) :
        s₁.mem.readW (wordAddr (s₁.gpr .r0) j) 32 = s.mem.readW (wordAddr (s.gpr .r0) j) 32 := by
      rw [keep₁ .r0 (by decide)]
      apply frame₁.readW (r := ⟨wordAddr (s.gpr .r0) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    have hk₁ : keyWord s₁ = k := by
      unfold keyWord
      rw [hword 0 (by decide), hword 1 (by decide)]
      exact hk
    have hread₁ : ∀ j < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .r0) j) 4 := by
      rw [rd₁, wr₁, keep₁ .r0 (by decide)]
      exact hread
    have hsep₁ : ∀ j < 2, (⟨wordAddr (s₁.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ .r0 (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ .r2 (by decide)) (keep₁ .r2 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r10 = s.gpr .r10 ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [foldl_xor_start]
  exact congrArg (l ^^^ ·) (by
    simpa only [contribution, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq] using
      boxPieces_eq_roundFunction r (k.setWidth 48))

def roundOuterKept : List Reg := [.r0, .r1, .r2, .r3, .r9]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r10 = s.gpr .r11 ∧ s'.gpr .r11 = s.gpr .r10 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.Arm.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · simp only [mem_setReg]
  · intro q hq
    have hneq : q ≠ .lr ∧ q ≠ .r10 ∧ q ≠ .r11 := by revert hq; cases q <;> decide
    simp only [gpr_setReg, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r11 (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
  · intro q hq
    have hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.Arm
