import VerifiedGarbage.Proof.TripleDes.X86.Round
import VerifiedGarbage.Proof.Framework.X86.RegUpd

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundKeyPtr (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 4) 32

def roundKeyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (roundKeyPtr s) 1) 32 ++
    s.mem.readW (wordAddr (roundKeyPtr s) 0) 32

structure BoxPre (s : State) : Prop where
  scratch : Ok sboxCfg s
  read : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (roundKeyPtr s) j) 4
  disjoint : ∀ j < 2, (⟨wordAddr (roundKeyPtr s) j, 4⟩ : Region).Disjoint (spillRegion s)
  sep : ∀ k < 128, ∀ j < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (roundKeyPtr s) j) 4

theorem pointerLoad_ok (s : State) (hok : Ok sboxCfg s) :
    exec (.mov .edx (.mem (memOp .ebp 16))) s = some (s.setReg .edx (roundKeyPtr s)) := by
  have hw := hok.slotIn 4 (by decide)
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, hmem, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hmem, hc⟩
  simp only [exec, readSrc, State.load32, memOp, State.ea]
  change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 then
    some (roundKeyPtr s) else none).map (s.setReg .edx) = _
  simp only [hr, ite_true, Option.map_some]

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution on IA-32. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (pre : BoxPre s) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ boxPiece i
        (Spec.TripleDes.sBox i (roundChunk i (s.gpr .edi) ((roundKeyWord s).setWidth 48))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  let s₀ := s.setReg .edx (roundKeyPtr s)
  have inputOk : Ok inputCfg s₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk; exact pre.scratch.slotIn k hk
    · intro j hj; exact pre.read j hj
    · exact pre.scratch.fit
    · intro k hk j hj; exact pre.sep k hk j hj
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, keep₁, frame₁⟩ := roundInput_chunk i hi s₀ inputOk
  have hok₁ : Ok sboxCfg s₁ := pre.scratch.congr
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)))
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide))) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have kept₂ : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi], s₂.gpr r = s₁.gpr r := by
    intro r hr; apply keep₂ r
    revert hr; cases r <;> decide
  have hok₂ : Ok outputCfg s₂ := hok₁.congr
    (kept₂ .ebp (by decide)) (kept₂ .ebp (by decide)) rd₂ wr₂
  have hbits : ∀ j < 4,
      (s₂.mem.readW (wordAddr (s₂.gpr .ebp) (16 + j)) 32).getLsbD 0 =
        (Spec.TripleDes.sBox i (roundChunk i (s.gpr .edi)
          ((roundKeyWord s).setWidth 48))).getLsbD j := by
    intro j hj
    rw [kept₂ .ebp (by decide), bits j hj 0 (by decide), chunk]
    rfl
  obtain ⟨s₃, run₃, value, rd₃, wr₃, keep₃, frame₃⟩ := roundOutput_piece i hi s₂ hok₂ _ hbits
  have region₁ : spillRegion s₁ = spillRegion s := by
    simp only [spillRegion, keep₁ .ebp (by decide), s₀, gpr_setReg, reduceCtorEq, ite_false]
  have region₂ : spillRegion s₂ = spillRegion s := by
    simp only [spillRegion, kept₂ .ebp (by decide), keep₁ .ebp (by decide), s₀,
      gpr_setReg, reduceCtorEq, ite_false]
  have frame₂ := sbox_spillFrame i hi s₁ s₂ hok₁.fit run₂
  rw [region₁] at frame₂
  rw [region₂] at frame₃
  have hframe₁ : Frame [spillRegion s] s.mem s₁.mem := frame₁
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_,
    hframe₁.trans (frame₂.trans frame₃)⟩
  · simp only [box, sboxInputs, runBoxes_append, runBlock_cons, runBlock_nil,
      pointerLoad_ok s pre.scratch, runStep_some, s₀, run₁, Option.bind_some, run₂, run₃]
  · rw [value, kept₂ .esi (by decide), keep₁ .esi (by decide)]
    rfl
  · intro r hr
    have hr₃ : r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx] := by
      revert hr; cases r <;> decide
    have hr₂ : r ∈ [Reg.esp, .ebp, .esi, .edi] := by
      revert hr; cases r <;> decide
    have hr₁ : r ∈ [Reg.esp, .ebp, .esi, .edi, .edx] := by
      revert hr; cases r <;> decide
    rw [keep₃ r hr₃, kept₂ r hr₂, keep₁ r hr₁]
    exact gpr_setReg_of_ne s _ (by revert hr; cases r <;> decide)
end VG.Proof.TripleDes.X86
