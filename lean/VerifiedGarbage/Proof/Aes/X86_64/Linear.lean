import VerifiedGarbage.Impl.Aes.X86_64.Linear
import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Aes.X86_64.Sbox
import VerifiedGarbage.Proof.Aes.Bitsliced

/-!
# The linear layers of bitsliced AES on x86-64

Untrusted: everything here is checked by Lean.

Each layer is checked by evaluation over the lane domain
(`Framework/X86_64/Linear.lean`): the kernel runs it on the input words
as atoms and compares every output bit with the XOR of input bits given
here. Position `p = 16r + 4c + b` of a word of the bitsliced state is byte
`r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

/-- The memory of the layers: masks in the slots at `r9`, and for
AddRoundKey the round key at `kp`. -/
def linCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-- `toBs`: bit `j` of byte `i` of block `b`, from bit `8 (i mod 8) + j`
of word `b + 4 ⌊i / 8⌋`. -/
def toBsG (j p : Nat) : List Nat := [64 * (p % 4 + 4 * (idx p / 8)) + (8 * (idx p % 8) + j)]

/-- `fromBs`: the inverse. -/
def fromBsG (k t : Nat) : List Nat := [64 * (t % 8) + pos (k % 4) (t / 8 + 8 * (k / 4))]

def srG (j p : Nat) : List Nat := [64 * j + srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 64 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [64 * j + p, 64 * (8 + j) + p]

theorem toBs_check : check (lanes 64 9) linCfg (linExt 0) toBs (linEnv qIns) (linPost 9 (qOuts toBsG)) = true := by
  decide +kernel

theorem fromBs_check :
    check (lanes 64 9) linCfg (linExt 0) fromBs (linEnv qIns) (linPost 9 (qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    check (lanes 64 9) linCfg (linExt 0) shiftRows (linEnv qIns) (linPost 9 (qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    check (lanes 64 9) linCfg (linExt 0) mixColumns (linEnv qIns) (linPost 9 (qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    check (lanes 64 10) arkCfg (linExt 8) addRoundKey (linEnv qIns) (linPost 10 (qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem writes_rest {is : List Instr}
    (h : [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all (fun r => is.all fun i => i.dst != some r) = true)
    (r : Reg) (hr : r ∉ sboxWrites) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp h r (not_sboxWrites r hr)

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : check (lanes 64 k) c (linExt xb) is (linEnv qIns) (linPost k (qOuts g)) = true)
    (hk : 512 ≤ 2 ^ k)
    (hw : [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all (fun r => is.all fun i => i.dst != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64) (hW : ∀ i < 8, W i = s.gpr (q i))
    (hext : ∀ j < c.exts,
      64 * (xb + j) + 64 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 64) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (s'.gpr (q j)).getLsbD p = xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hri => by
    simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega, hW i hi⟩) hext
  have hmem : ∀ j < 8, (q j, g j) ∈ qOuts g := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj p hp => hout (q j) (g j) (hmem j hj) p hp, hrd, hwr,
    fun r hr => hoth r (writes_rest hw r hr), hfr⟩

/-- The words of the state registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

theorem toBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p =
        (Q s (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear toBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega)]

/-- `toBs` leaves `t1` alone. -/
theorem toBs_keeps_t1 {s s' : State} (hok : Ok linCfg s) (h : runBlock isa toBs s = some s') :
    s'.gpr t1 = s.gpr t1 := by
  obtain ⟨s'', hs'', -, -, -, hoth, -⟩ := linear_ok toBs_check hok (Q s) (fun r i hri => by
    simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
    obtain ⟨i, hi, rfl, rfl⟩ := hri
    exact ⟨by omega, rfl⟩) (fun j hj => by simp [linCfg] at hj)
  rw [run_unique h hs'']
  exact hoth t1 (by decide +kernel)

theorem fromBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ k < 8, ∀ t < 64, (Q s' k).getLsbD t = (Q s (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear fromBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega)]

theorem shiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem xorBits_map (W : Nat → BitVec 64) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 64) :
    xorBits W (l.map fun wt => 64 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

theorem mixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear mixColumns_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) j) 64

theorem addRoundKey_ok {s : State} (hok : Ok arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = ((Q s j).getLsbD p ^^ (keyWord s j).getLsbD p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 64 := fun i => if i < 8 then Q s i else keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := q_linear addRoundKey_check (by decide) (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.X86_64
