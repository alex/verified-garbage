import VerifiedGarbage.Proof.TripleDes.X86_64.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Spills

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution, including E/key input extraction,
the Boolean circuit, and P output placement. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 ^^^
        (boxPiece i (Spec.TripleDes.sBox i
          (roundChunk i ((s.gpr .r13).setWidth 32)
            ((s.mem.readW (s.gpr .rdi) 64).setWidth 48)))).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, mem₁, keep₁⟩ := roundInput_chunk i hi s hread
  have kept₁ : ∀ r ∈ .r12 :: roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (roundInput_keep i hi r hr)
  have hok₁ : Ok sboxCfg s₁ := hok.congr
    (kept₁ .rdx (by decide)) (kept₁ .rdx (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (roundChunk i ((s.gpr .r13).setWidth 32)
        ((s.mem.readW (s.gpr .rdi) 64).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, mem₃, keep₃⟩ := roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_, ?_⟩
  · simp only [box, runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ .r12 (by decide), kept₁ .r12 (by decide)]
  · intro r hr
    rw [keep₃ r (roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; cases r <;> decide
  · have hf := sbox_spillFrame i hi s₁ s₂ run₂
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, kept₁ .rdx (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.X86_64
