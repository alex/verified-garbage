import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundFunction
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64

def contribution (r k : BitVec 64) (i : Nat) : BitVec 64 :=
  (boxPiece i (Spec.TripleDes.sBox i
    (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 64

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr .x20 = r) (hk : s.mem.readW (s.gpr .x22) 64 = k)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8)
    (hsep : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .x19 = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .x19) ∧
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
      simp only [spillRegion, keep₁ .x2 (by decide)]
    have hr₁ : s₁.gpr .x20 = r := (keep₁ .x20 (by decide)).trans hr
    have hk₁ : s₁.mem.readW (s₁.gpr .x22) 64 = k := by
      rw [keep₁ .x22 (by decide)]
      refine Eq.trans (frame₁.readW (r := ⟨s.gpr .x22, 8⟩) ?_ ?_ (by decide)) hk
      · simp [Region.Contains]
      · intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact hsep
    have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x22) 8 := by
      rw [rd₁, wr₁, keep₁ .x22 (by decide)]
      exact hread
    have hsep₁ : (⟨s₁.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ .x22 (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ .x2 (by decide)) (keep₁ .x2 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .x19 = s.gpr .x19 ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r k : BitVec 64) (l : BitVec 64) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ (Spec.TripleDes.roundFunction (r.setWidth 32) (k.setWidth 48)).zeroExtend 64 := by
  rw [foldl_xor_start]
  have hf := foldl_xor_extend (List.range 8)
    (fun i => boxPiece i (Spec.TripleDes.sBox i
      (roundChunk i (r.setWidth 32) (k.setWidth 48)))) 0
  have hz : (0 : BitVec 32).setWidth 64 = 0 := BitVec.setWidth_zero 64 32
  have hinit := congrArg (fun b : BitVec 64 =>
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) b) hz
  have hg := congrArg (BitVec.setWidth 64)
    (boxPieces_eq_roundFunction (r.setWidth 32) (k.setWidth 48))
  exact congrArg (fun x => l ^^^ x) ((hinit.symm.trans hf).trans hg)

def roundOuterKept : List Reg := [.x0, .x1, .x2, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .x19 = s.gpr .x20 ∧ s'.gpr .x20 = s.gpr .x19 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.AArch64.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec,
      show (0 : Nat) < 4096 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, BitVec.add_zero, gpr_write]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq]; rfl
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · simp only [mem_write]
  · intro q hq
    have hneq : q ≠ .x3 ∧ q ≠ .x19 ∧ q ≠ .x20 := by
      revert hq; cases q <;> decide
    simp only [gpr_write, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .x22) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8)
    (hsep : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .x19 = r.setWidth 64 ∧
      s'.gpr .x20 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r.setWidth 64) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .x20 (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
    have hwidth : (r.setWidth 64).setWidth 32 = r := by simp
    rw [hwidth]
    exact BitVec.setWidth_xor.symm
  · intro q hq
    have hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.AArch64
