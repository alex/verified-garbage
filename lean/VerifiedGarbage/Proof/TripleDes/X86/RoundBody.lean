import VerifiedGarbage.Proof.TripleDes.X86.Box
import VerifiedGarbage.Proof.TripleDes.X86.RoundFunction

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

theorem roundKeyPtr_frame {s s' : State} (pre : BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (frame : Frame [spillRegion s] s.mem s'.mem) :
    roundKeyPtr s' = roundKeyPtr s := by
  unfold roundKeyPtr
  rw [base]
  apply frame.readW (r := ⟨wordAddr (s.gpr .ebp) 4, 4⟩) (Region.contains_self _ _)
    (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  change (⟨addr (s.gpr .ebp) 16, 4⟩ : Region).Disjoint (spillRegion s)
  rw [addr_eq (by have h := pre.scratch.fit; change (s.gpr .ebp).toNat + 512 ≤ _ at h; omega)]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem BoxPre.frame {s s' : State} (pre : BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (frame : Frame [spillRegion s] s.mem s'.mem) :
    BoxPre s' ∧ roundKeyWord s' = roundKeyWord s := by
  have ptr := roundKeyPtr_frame pre base frame
  have region : spillRegion s' = spillRegion s := by simp only [spillRegion, base]
  constructor
  · refine ⟨pre.scratch.congr base base rd wr, ?_, ?_, ?_⟩
    · rw [rd, wr, ptr]; exact pre.read
    · rw [ptr, region]; exact pre.disjoint
    · rw [base, ptr]; exact pre.sep
  · unfold roundKeyWord
    rw [ptr]
    have hword (j : Nat) (hj : j < 2) :
        s'.mem.readW (wordAddr (roundKeyPtr s) j) 32 =
          s.mem.readW (wordAddr (roundKeyPtr s) j) 32 :=
      frame.readW (r := ⟨wordAddr (roundKeyPtr s) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact pre.disjoint j hj) (by decide)
    rw [hword 0 (by decide), hword 1 (by decide)]

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  boxPiece i (Spec.TripleDes.sBox i (roundChunk i r (k.setWidth 48)))

theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (pre : BoxPre s)
    (hr : s.gpr .edi = r) (hk : roundKeyWord s = k) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .esi = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .esi) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.esp, .ebp, .edi], s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi := hindices i List.mem_cons_self
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, keep₁, frame₁⟩ := box_ok i hi s pre
    obtain ⟨pre₁, key₁⟩ := pre.frame (keep₁ .ebp (by decide)) rd₁ wr₁ frame₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ pre₁
      ((keep₁ .edi (by decide)).trans hr) (key₁.trans hk)
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      fun q hq => (keep₂ q hq).trans (keep₁ q hq), ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .esi = s.gpr .esi ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · have hregion : spillRegion s₁ = spillRegion s := by
        simp only [spillRegion, keep₁ .ebp (by decide)]
      rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [foldl_xor_start]
  exact congrArg (l ^^^ ·) (boxPieces_eq_roundFunction r (k.setWidth 48))

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .esi = s.gpr .edi ∧ s'.gpr .edi = s.gpr .esi ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp := by
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true,
    rd_setReg, wr_setReg, mem_setReg]

theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : roundKeyWord s = k) (pre : BoxPre s) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) r k s pre hr hk
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, base₂, sp₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans (keep₁ .ebp (by decide)), sp₂.trans (keep₁ .esp (by decide)), ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .edi (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
  · rw [mem₂]; exact frame₁
end VG.Proof.TripleDes.X86
