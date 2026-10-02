import VerifiedGarbage.Proof.TripleDes.X86.RoundInput
import VerifiedGarbage.Proof.TripleDes.X86.RoundOutput
import VerifiedGarbage.Proof.TripleDes.X86.Sbox
import VerifiedGarbage.Proof.TripleDes.X86.Spills
import VerifiedGarbage.Proof.TripleDes.Permutation

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 32) (a : Nat) (ha : a < 32) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

def keyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .edx) 1) 32 ++ s.mem.readW (wordAddr (s.gpr .edx) 0) 32

theorem bitOf_key (s : State) (a : Nat) (ha : a < 64) :
    bitOf (fun k => if k = 0 then s.gpr .edi else
      s.mem.readW (wordAddr (s.gpr .edx) (k - 1)) 32) (32 + a) =
    (keyWord s).getLsbD a := by
  simp only [bitOf, keyWord, BitVec.getLsbD_append]
  by_cases h : a < 32
  · have hd : (32 + a) / 32 = 1 := by omega
    simp only [h, ite_true, hd, Nat.add_mod_left, Nat.mod_eq_of_lt h]
    rfl
  · have hd : (32 + a) / 32 = 2 := by omega
    have hm : (32 + a) % 32 = a - 32 := by omega
    simp only [h, ite_false, hd, hm]
    rfl

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 32) (k : BitVec 64) :
    (roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega
  have hsource : 32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ Spec.TripleDes.expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega
    have := hb _ hpos
    omega
  simp only [roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.TripleDes.permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

theorem input_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi, .edx].all (fun r =>
      (instrs (inputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem input_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .esi, .edi, .edx]) :
    (sboxInputBits i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (input_keeps i hi) r hr
  rw [inputLiteral_eq i hi] at h
  exact h

theorem input_spillSafe : ∀ i < 8,
    (instrs (inputLiterals.getD i (.block []))).all spillSafe = true := by decide +kernel

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State) (hok : Ok inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      inputAt s' 0 = roundChunk i (s.gpr .edi) ((keyWord s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := roundInput_ok i hi s hok
  have kept : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r :=
    fun r hr => keep r (input_keep i hi r hr)
  have safe := input_spillSafe i hi
  rw [inputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, kept, (spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and,
    kept .ebp (by decide)]
  rw [bits j hj 0 (by decide), ← BitVec.setWidth_eq (s.gpr .edi), roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := roundInput_bounds i hi j hj
  simp only [inputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_low _ _ hr, roundInputs, ite_true]
  have hkey : bitOf (roundInputs s) (32 + (47 - (6 * i + 5 - j))) =
      (keyWord s).getLsbD (47 - (6 * i + 5 - j)) := bitOf_key s _ hk
  rw [hkey]

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if boxSource p / 4 = i then
    b.getLsbD (3 - boxSource p % 4) else false

theorem outputBits_shape : ∀ i < 8, ∀ p < 32,
    outputBits i p = [128 + p] ++
      (if boxSource p / 4 = i then [32 * (3 - boxSource p % 4)] else []) := by
  decide +kernel
theorem output_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx].all (fun r =>
      (instrs (outputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem output_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx]) :
    (sboxOutputs i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (output_keeps i hi) r hr
  rw [outputLiteral_eq i hi] at h
  exact h

theorem output_spillSafe : ∀ i < 8,
    (instrs (outputLiterals.getD i (.block []))).all spillSafe = true := by decide +kernel

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (hok : Ok outputCfg s)
    (b : BitVec 4)
    (hb : ∀ j < 4,
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ boxPiece i b ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := roundOutput_ok i hi s hok
  have safe := output_spillSafe i hi
  rw [outputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, fun r hr => keep r (output_keep i hi r hr),
    (spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, outputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, List.cons_append, List.nil_append, xorBits_cons]
  have hleft : bitOf (roundOutputs s) (128 + p) = (s.gpr .esi).getLsbD p := by
    have h := VG.Proof.TripleDes.X86.Linear.bitOf_word (roundOutputs s) 4 p hp
    exact h
  rw [hleft]
  by_cases h : boxSource p / 4 = i
  · simp only [h, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false]
    have hj : 3 - boxSource p % 4 < 4 := by omega
    have hjne : 3 - boxSource p % 4 ≠ 4 := by omega
    have hbit := VG.Proof.TripleDes.X86.Linear.bitOf_word (roundOutputs s)
      (3 - boxSource p % 4) 0 (by decide)
    simp only [Nat.add_zero] at hbit
    rw [hbit]
    simp only [roundOutputs, hjne, ite_false, hb _ hj, boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and, h, ite_true]
  · simp only [h, ite_false, xorBits_nil, Bool.xor_false, boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and]
end VG.Proof.TripleDes.X86
