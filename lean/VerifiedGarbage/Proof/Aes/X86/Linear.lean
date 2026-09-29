import VerifiedGarbage.Impl.Aes.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Aes.X86.Sbox
import VerifiedGarbage.Proof.Aes.Ct32.Layers

/-!
# The linear layers of bitsliced AES on x86 (32-bit)

Untrusted: everything here is checked by Lean.

Each layer is checked by evaluation over the lane domain
(`Framework/X86/Linear.lean`): the kernel runs it on the input words (the
slots `0 … 7`, and for AddRoundKey the round key at `kp`) as atoms and
compares every output bit with the XOR of input bits given in
`Proof/Aes/Ct32/Layers.lean`. Position `p = 8r + 2c + b` of a word of the
bitsliced state is byte `r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32

/-- AddRoundKey's memory: the state, and the round key at `kp`. -/
def arkCfg : Cfg := { base := sb, slots := 8, ext := kp, exts := 8 }

/-- The state slots hold input words `0 … 7`. -/
def qIns : List (Nat × Nat) := (List.range 8).map fun k => (k, k)

/-- The output slots `j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (j, g j)

theorem ortho_toBs_check :
    check (lanes 32 8) linCfg (linExt 0) ortho (linEnv qIns) (linPost 64 8 (qOuts toBsG)) = true := by
  decide +kernel

theorem ortho_fromBs_check :
    check (lanes 32 8) linCfg (linExt 0) ortho (linEnv qIns) (linPost 64 8 (qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    check (lanes 32 8) linCfg (linExt 0) shiftRows (linEnv qIns) (linPost 64 8 (qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    check (lanes 32 8) linCfg (linExt 0) mixColumns (linEnv qIns) (linPost 64 8 (qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    check (lanes 32 9) arkCfg (linExt 8) addRoundKey (linEnv qIns) (linPost 8 9 (qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : check (lanes 32 k) c (linExt xb) is (linEnv qIns) (linPost c.slots k (qOuts g)) = true)
    (hk : 256 ≤ 2 ^ k) (hcb : c.base = sb)
    (hw : [Reg.esp, .esi, .edi].all (fun r => is.all fun i => i.dst != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32) (hW : ∀ i < 8, W i = Q s i)
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok hchk hok W (fun j i hji _ => by
    simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
    obtain ⟨i, hi, rfl, rfl⟩ := hji
    exact ⟨by omega, by rw [hW i hi, hcb]⟩) hext
  have hmem : ∀ j < 8, (j, g j) ∈ qOuts g := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  have hsb : s'.gpr sb = s.gpr sb := hoth sb (keeps_rest hw sb (by decide))
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, fun r hr => hoth r (keeps_rest hw r hr), hfr⟩
  have := hout j (g j) (hmem j hj) p hp
  rw [hcb] at this
  rw [Q, hsb]; exact this

theorem toBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p =
        (Q s (p % 2 + 2 * (idx p / 4))).getLsbD (8 * (idx p % 4) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear ortho_toBs_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega)]

theorem fromBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ k < 8, ∀ t < 32, (Q s' k).getLsbD t = (Q s (t % 8)).getLsbD (pos (k % 2) (t / 8 + 4 * (k / 2)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear ortho_fromBs_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega)]

theorem shiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = termsXor (Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear mixColumns_check (by decide) rfl
    (by decide +kernel) hok (Q s) (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
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
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i < 8 then Q s i else keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := q_linear addRoundKey_check (by decide) rfl
    (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.X86
