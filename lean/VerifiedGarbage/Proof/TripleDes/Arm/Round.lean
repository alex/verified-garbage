import VerifiedGarbage.Proof.TripleDes.Arm.RoundLit
import VerifiedGarbage.Proof.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.Arm.Linear

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm

noncomputable def sboxInputsLiterals : Array (Prog isa) :=
  #[sboxInputs0.lit, sboxInputs1.lit, sboxInputs2.lit, sboxInputs3.lit, sboxInputs4.lit, sboxInputs5.lit, sboxInputs6.lit, sboxInputs7.lit]

noncomputable def sboxInputsLiteral (i : Nat) : Prog isa :=
  sboxInputsLiterals.getD i (.block [])

noncomputable def sboxOutputsLiterals : Array (Prog isa) :=
  #[sboxOutputs0.lit, sboxOutputs1.lit, sboxOutputs2.lit, sboxOutputs3.lit, sboxOutputs4.lit, sboxOutputs5.lit, sboxOutputs6.lit, sboxOutputs7.lit]

noncomputable def sboxOutputsLiteral (i : Nat) : Prog isa :=
  sboxOutputsLiterals.getD i (.block [])

def roundInputCfg : Cfg := { base := .r2, slots := 0, ext := .r0, exts := 2 }
def roundInputRegs : List (Reg × Nat) := [(.r11, 0)]

def roundInputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 32 + (47 - k)]
  else []

def roundInputPost (i : Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 6).map fun j => (q j, roundInputBits i j)

theorem roundInput_check : ∀ i < 8,
    check (lanes 32 7) roundInputCfg (linExt 1) (instrs (sboxInputsLiteral i))
      (linEnv roundInputRegs) (linPost 7 (roundInputPost i)) = true := by
  decide +kernel

def roundOutputCfg : Cfg := { base := .r2, slots := 0, ext := .r2, exts := 0 }
def roundOutputRegs : List (Reg × Nat) :=
  [(.r10, 0)] ++ (List.range 4).map fun j => (q j, j + 1)

def roundOutputBits (i p : Nat) : List Nat :=
  [p] ++ ((List.range 4).filterMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then some (32 * (j + 1)) else none)

theorem roundOutput_check : ∀ i < 8,
    check (lanes 32 9) roundOutputCfg (linExt 5) (instrs (sboxOutputsLiteral i))
      (linEnv roundOutputRegs) (linPost 9 [(.r10, roundOutputBits i)]) = true := by
  decide +kernel

theorem sboxInputsLiteral_eq : ∀ i < 8,
    sboxInputsLiteral i = .block (sboxInputs i)
  | 0, _ => sboxInputs0.lit_eq.symm
  | 1, _ => sboxInputs1.lit_eq.symm
  | 2, _ => sboxInputs2.lit_eq.symm
  | 3, _ => sboxInputs3.lit_eq.symm
  | 4, _ => sboxInputs4.lit_eq.symm
  | 5, _ => sboxInputs5.lit_eq.symm
  | 6, _ => sboxInputs6.lit_eq.symm
  | 7, _ => sboxInputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundInputCfg_ok (s : State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) : Ok roundInputCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [roundInputCfg] at hk
  · exact hread
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [roundInputCfg] at hk

/-- The extraction block reads just one round key and forms six Boolean
input words. It does not change memory, access permissions or other registers. -/
theorem roundInput_ok (i : Nat) (hi : i < 8) (s : State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      (∀ j < 6, ∀ p < 32, (s'.gpr (q j)).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r11
          else s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32) (roundInputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundInput_check i hi
  rw [sboxInputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 32 := fun k =>
    if k = 0 then s.gpr .r11 else s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundInputCfg_ok s hread) W (fun r k h => by
      simp only [roundInputRegs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩) (fun j hj => by
      have hb : j < 2 := hj
      refine ⟨by omega, ?_⟩
      simp only [W, Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and, ite_false, Nat.add_sub_cancel_left, roundInputCfg])
  refine ⟨s', hs', fun j hj p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out (q j) (roundInputBits i j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, roundInputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 32) (a : Nat) (ha : a < 32) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

def keyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .r0) 1) 32 ++ s.mem.readW (wordAddr (s.gpr .r0) 0) 32

theorem bitOf_key (s : State) (a : Nat) (ha : a < 64) :
    bitOf (fun k => if k = 0 then s.gpr .r11 else
      s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32) (32 + a) =
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

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      inputAt s' 0 = roundChunk i ((s.gpr .r11).setWidth 32)
        ((keyWord s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := roundInput_ok i hi s hread
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  rw [bits j hj 0 (by decide), roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := roundInput_bounds i hi j hj
  simp only [roundInputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_low _ _ hr, bitOf_key s _ hk, ite_true]

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if boxSource p / 4 = i then
    b.getLsbD (3 - boxSource p % 4) else false

theorem roundOutputBits_shape : ∀ i < 8, ∀ p < 32,
    roundOutputBits i p = [p] ++
      (if p < 32 ∧ boxSource p / 4 = i then
        [32 * (4 - boxSource p % 4)] else []) := by
  decide +kernel

theorem sboxOutputsLiteral_eq : ∀ i < 8,
    sboxOutputsLiteral i = .block (sboxOutputs i)
  | 0, _ => sboxOutputs0.lit_eq.symm
  | 1, _ => sboxOutputs1.lit_eq.symm
  | 2, _ => sboxOutputs2.lit_eq.symm
  | 3, _ => sboxOutputs3.lit_eq.symm
  | 4, _ => sboxOutputs4.lit_eq.symm
  | 5, _ => sboxOutputs5.lit_eq.symm
  | 6, _ => sboxOutputs6.lit_eq.symm
  | 7, _ => sboxOutputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundOutputCfg_ok (s : State) : Ok roundOutputCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [roundOutputCfg] at hk
  · intro k hk; simp [roundOutputCfg] at hk
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [roundOutputCfg] at hk

/-- Deposit the four low S-box bits into L, at P's fixed destinations. -/
theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : State) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 32, (s'.gpr .r10).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r10 else s.gpr (q (k - 1)))
          (roundOutputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundOutput_check i hi
  rw [sboxOutputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 32 := fun k =>
    if k = 0 then s.gpr .r10 else s.gpr (q (k - 1))
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundOutputCfg_ok s) W (fun r k h => by
      simp only [roundOutputRegs, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, List.mem_map, List.mem_range] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨j, hj, heq⟩
      · exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by omega, ?_⟩
        simp [W]) (fun j hj => by simp [roundOutputCfg] at hj)
  refine ⟨s', hs', fun p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out .r10 (roundOutputBits i) (by simp) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, roundOutputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem bitOf_word (W : Nat → BitVec 32) (j : Nat) :
    bitOf W (32 * j) = (W j).getLsbD 0 := by
  simp [bitOf]

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (b : BitVec 4)
    (hb : ∀ j < 4, (s.gpr (q j)).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .r10 = s.gpr .r10 ^^^ (boxPiece i b).zeroExtend 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := roundOutput_ok i hi s
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, roundOutputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and]
  simp only [List.cons_append, List.nil_append, xorBits_cons, bitOf_low _ _ hp, ite_true]
  by_cases h : p < 32 ∧ boxSource p / 4 = i
  · simp only [h]
    have hj : 3 - boxSource p % 4 < 4 := by omega
    simp
    rw [bitOf_word]
    have hn : 4 - boxSource p % 4 ≠ 0 := by omega
    have heq : 4 - boxSource p % 4 - 1 = 3 - boxSource p % 4 := by omega
    simp only [hn, ite_false, heq]
    rw [hb _ hj]
    simp only [boxPiece, getLsbD_ofBits, h.1, h.2, decide_true, Bool.true_and, ite_true]
  · have hs : boxSource p / 4 ≠ i := by omega
    simp only [hs, ite_false, xorBits_nil, boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and, and_false]

def roundKept : List Reg := [.r0, .r1, .r2, .r3, .r9, .r11]

theorem roundInput_keeps : ∀ i < 8, (.r10 :: roundKept).all
    (fun r => (instrs (sboxInputsLiteral i)).all fun op => dstOf op != some r) = true := by
  decide +kernel

theorem roundOutput_keeps : ∀ i < 8, roundKept.all
    (fun r => (instrs (sboxOutputsLiteral i)).all fun op => dstOf op != some r) = true := by
  decide +kernel

theorem roundInput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ .r10 :: roundKept) :
    (sboxInputs i).all (fun op => dstOf op != some r) = true := by
  have h := List.all_eq_true.mp (roundInput_keeps i hi) r hr
  rw [sboxInputsLiteral_eq i hi] at h
  exact h

theorem roundOutput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ roundKept) :
    (sboxOutputs i).all (fun op => dstOf op != some r) = true := by
  have h := List.all_eq_true.mp (roundOutput_keeps i hi) r hr
  rw [sboxOutputsLiteral_eq i hi] at h
  exact h

end VG.Proof.TripleDes.Arm
