import VerifiedGarbage.Impl.Aes.Arm.Linear
import VerifiedGarbage.Proof.Aes.Arm.Sbox

/-!
# The linear layers of bitsliced AES on ARMv7

Each layer is checked by evaluation over the lane domain
(`Framework/Arm/Linear.lean`): the kernel runs it on the input words as
atoms and compares every output bit with the XOR of input bits given in
`Proof/Aes/Arm/Bitsliced.lean`. Position `p = 8r + 2c + b` of a word of the
bitsliced state is byte `r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm

/-- The memory of the layers: the S-box's slots, and for AddRoundKey the
round key at `kp`. -/
abbrev linCfg : Cfg := sboxCfg
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

theorem ortho_check :
    check (lanes 32 8) linCfg (linExt 0) ortho (linEnv qIns) (linPost 8 (qOuts orthoG)) = true := by
  decide +kernel

theorem shiftRows_check :
    check (lanes 32 8) linCfg (linExt 0) shiftRows (linEnv qIns) (linPost 8 (qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    check (lanes 32 8) linCfg (linExt 0) mixColumns (linEnv qIns) (linPost 8 (qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    check (lanes 32 9) arkCfg (linExt 8) addRoundKey (linEnv qIns) (linPost 9 (qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : check (lanes 32 k) c (linExt xb) is (linEnv qIns) (linPost k (qOuts g)) = true)
    (hk : 256 ≤ 2 ^ k)
    (hw : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32) (hW : ∀ i < 8, W i = s.gpr (q i))
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 32, (s'.gpr (q j)).getLsbD p = Straight.xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hri => by
    simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega, hW i hi⟩) hext
  have hmem : ∀ j < 8, (q j, g j) ∈ qOuts g := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (q j) (g j) (hmem j hj) p hp, hrd, hwr, hsp,
    fun r hr => hoth r (writes_rest hw r hr), hfr⟩

/-- The words of the state registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 32 := s.gpr (q i)

theorem ortho_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s (p % 8)).getLsbD (8 * (p / 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear ortho_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, orthoG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by omega)]

theorem shiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = termsXor (Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear mixColumns_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [sboxCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) j) 32

theorem addRoundKey_ok {s : State} (hok : Ok arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = ((Q s j).getLsbD p ^^ (keyWord s j).getLsbD p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i < 8 then Q s i else keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := q_linear addRoundKey_check (by decide) (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, Straight.xorBits_cons, Straight.xorBits_cons,
    Straight.xorBits_nil, Bool.xor_false, Straight.bitOf_word _ _ _ hp,
    Straight.bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.Arm
