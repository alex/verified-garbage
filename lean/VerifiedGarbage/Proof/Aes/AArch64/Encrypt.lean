import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
import VerifiedGarbage.Impl.Aes.AArch64.Linear
import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Impl.Aes.AArch64.Sbox
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Straight
import VerifiedGarbage.Proof.Framework.Offset

section

section

/-!
# The bitsliced S-box on AArch64

Untrusted: everything here is checked by Lean.

`sboxCode` only combines words bitwise (and builds all ones with `movz` and
`sub`), so it computes the same Boolean function at each of the 64 bit
positions: the kernel evaluates it once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's S-box
on the same tables (`sboxT`, proved right in `Proof/Aes/SboxSpec.lean`).
`sbox_ok` then gives, at every bit position `p`, the S-box of the byte
formed by bit `p` of the eight words.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (sbox)

/-- The S-box's memory: its spill slots, at `x5`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((sboxT inTs).getD j 0)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers of AES may write: the state, the S-box's
temporaries and all ones, and the linear layers' masks and temporaries. -/
def layerWrites : List Reg :=
  [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
   .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29]

/-- The registers outside `layerWrites`. -/
def layerKeep : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x30]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    (r : Reg) (hr : r ∉ layerWrites) : (is.all fun i => dstOf i != some r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((sboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp
  · simp [writes_rest (is := sboxCode) (by decide +kernel) r hr]

end VG.Proof.Aes.AArch64

end

/-!
# The linear layers of bitsliced AES on AArch64

Untrusted: everything here is checked by Lean.

Each layer is checked by evaluation over the lane domain
(`Framework/AArch64/Linear.lean`): the kernel runs it on the input words
as atoms and compares every output bit with the XOR of input bits given
here. Position `p = 16r + 4c + b` of a word of the bitsliced state is byte
`r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-- The memory of the layers: nothing in memory, and for
AddRoundKey the round key at `kp`. -/
def linCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

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

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : check (lanes 64 k) c (linExt xb) is (linEnv qIns) (linPost k (qOuts g)) = true)
    (hk : 512 ≤ 2 ^ k)
    (hw : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 64) (hW : ∀ i < 8, W i = s.gpr (q i))
    (hext : ∀ j < c.exts,
      64 * (xb + j) + 64 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 64) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (s'.gpr (q j)).getLsbD p = xorBits W (g j p)) ∧
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
abbrev Q (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

theorem toBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p =
        (Q s (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear toBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega)]

theorem fromBs_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ k < 8, ∀ t < 64, (Q s' k).getLsbD t = (Q s (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear fromBs_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega)]

theorem shiftRows_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := q_linear shiftRows_check (by decide) (by decide +kernel) hok (Q s)
    (fun _ _ => rfl) (fun j hj => by simp [linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
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
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
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

end VG.Proof.Aes.AArch64

end

/-!
# Encrypting four blocks, bitsliced, on AArch64

Untrusted: everything here is checked by Lean.

`encrypt4_ok`: from four blocks in the registers (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`), `encrypt4` leaves
the four ciphertexts, having written only the first 384 bytes of the
scratch buffer. The layers are composed from their proofs
(`Sbox.lean`, `Linear.lean`); the round loop's invariant is the
specification's `foldl` over the rounds done.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)

/-- The bitsliced round keys `0 … R` of the schedule `w`, from `K0`, 64 bytes each. -/
def KeysAt (m : Mem) (K0 : Addr) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (wordAddr (K0 + BitVec.ofNat 64 (64 * j)) k) 64) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `x5`) is
writable, and the round keys are in it, the last at byte `lastKey`. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨s₀.gpr sb, 2048⟩ : Region) ∈ s₀.wr
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  k0 : s₀.gpr .x0 = s₀.gpr sb + BitVec.ofNat 64 (1920 - 64 * R)
  keys : KeysAt s₀.mem (s₀.gpr .x0) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 384⟩] s₀.mem s.mem

theorem sb_not : sb ∉ layerWrites ∧ sb ≠ kp := by decide
theorem x0_not : Reg.x0 ∉ layerWrites ∧ Reg.x0 ≠ kp := by decide

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ sb_not.1 sb_not.2

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [⟨s.gpr sb, 384⟩] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

theorem Ctx.linOk {s₀ s : State} (hp : (⟨s₀.gpr sb, 2048⟩ : Region) ∈ s₀.wr) (hc : Ctx s₀ s) :
    Ok linCfg s :=
  Ok.of_region (r := ⟨s₀.gpr sb, 2048⟩) (by rw [hc.wr]; exact hp) (by simp [linCfg, hc.base])
    (by simp [linCfg]) (by simp [linCfg]) rfl

/-- The key area is outside what the layers write. -/
theorem keys_disjoint (b : Addr) : Region.Disjoint ⟨b + 1024, 1024⟩ ⟨b, 384⟩ :=
  Offset.disjoint_base (d := 1024) b (by omega) (by omega)

theorem addr3 (b : Addr) (x y z : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y + BitVec.ofNat 64 z = b + BitVec.ofNat 64 (x + y + z) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]

theorem off_contains (b : Addr) {base n len k : Nat} (h1 : base ≤ n) (h2 : n + k ≤ base + len)
    (h3 : base + len < 2 ^ 64) :
    (⟨b + BitVec.ofNat 64 base, len⟩ : Region).Contains (b + BitVec.ofNat 64 n) k := Offset.contains b h1 h2 h3

theorem key_contains (b : Addr) {R j k : Nat} (hR : R ≤ 14) (hj : j ≤ R) (hk : k < 8) :
    (⟨b + 1024, 1024⟩ : Region).Contains
      (wordAddr (b + BitVec.ofNat 64 (1920 - 64 * R) + BitVec.ofNat 64 (64 * j)) k) (64 / 8) := by
  simp only [wordAddr]
  rw [addr3]
  exact off_contains (base := 1024) b (by omega) (by omega) (by omega)

theorem keyRel_congr {K K' : Nat → BitVec 64} {rk : List Byte} (h : KeyRel K rk)
    (he : ∀ k < 8, K' k = K k) : KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    KeysAt s.mem (s₀.gpr .x0) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (key_contains _ hR hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact keys_disjoint _) (by decide)

theorem ark_cfg_ok {s : State} {b : Addr} {n : Nat} (hscr : (⟨b, 2048⟩ : Region) ∈ s.wr)
    (hk : s.gpr kp = b + BitVec.ofNat 64 n) (hn : n + 64 ≤ 2048) : Ok arkCfg s where
  slotIn k hk := by simp [arkCfg] at hk
  extIn k hk' := by
    simp only [arkCfg] at hk'
    refine ⟨⟨b, 2048⟩, List.mem_append_right _ hscr, ?_⟩
    have h := off_contains (base := 0) (n := n + 8 * k) (len := 2048) (k := 8) b (by omega) (by omega)
      (by omega)
    simp only [BitVec.add_zero] at h
    simpa [arkCfg, wordAddr, hk, BitVec.ofNat_add, BitVec.add_assoc] using h
  slots := by simp [arkCfg]
  sep k hk := by simp [arkCfg] at hk

/-! ## One layer at a time -/

/-- A layer that writes only `layerWrites` and the first 384 bytes of the
scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * 48⟩] s.mem s'.mem)
    (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hsp, hoth, hfr⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr hsp (fun r h _ => hoth r h) hfr) hP
    (hoth kp (by decide))⟩

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    midRounds w (m + 1) x = rnd w (m + 1) (midRounds w m x) := by
  simp [midRounds, List.range_succ, List.foldl_append]

theorem kp_step (K : Addr) (m : Nat) :
    K + BitVec.ofNat 64 (64 * m) + BitVec.ofNat 64 64 = K + BitVec.ofNat 64 (64 * (m + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * m + 64 = 64 * (m + 1) by omega]

theorem q_ne_kp (i : Nat) : q i ≠ kp := by
  unfold q; split <;> decide

theorem q_ne_t0 (i : Nat) : q i ≠ t0 := by
  unfold q; split <;> decide

/-- `add kp, kp, #64`. -/
theorem addKp_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 →
      (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [.addImm .x kp kp 64]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [Q, State.write, q_ne_kp i]

/-- `sub t0, kp, x5; sub t0, t0, #(lastKey - 64)`. -/
theorem cmpLast_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ i, Q s' i = Q s i) →
      s'.gpr t0 = s.gpr kp - s.gpr sb - BitVec.ofNat 64 (lastKey - 64) → P s') :
    WP isa (.block [.sub .x t0 kp sb, .subImm .x t0 t0 (lastKey - 64)]) s P := by
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, show exec (.sub .x t0 kp sb) s =
    some (s.write .x t0 (s.read .x kp - s.read .x sb)) from rfl, runStep_some, runBlock_cons,
    exec_subImm_x (by decide), runStep_some, runBlock_nil], h _ ?_ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r hr _ => by
      have : r ≠ t0 := fun h => hr (h ▸ by decide)
      simp [State.write, this]) (Frame.refl _ _)
  · simp [State.write, t0, kp]
  · intro i; simp [Q, State.write, q_ne_t0 i]
  · simp [State.write, State.read]

theorem t0_last (b : Addr) {R m : Nat} (hR : R ≤ 14) (hm : m + 1 < R) :
    (b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (lastKey - 64) != 0) =
      !decide (m + 2 = R) := by
  simp only [lastKey]
  by_cases h : m + 2 = R
  · have e : b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (1920 - 64) = 0 := by
      bv_omega
    rw [e]; simp [h]
  · have e : b + BitVec.ofNat 64 (1920 - 64 * R + 64 * (m + 1)) - b - BitVec.ofNat 64 (1920 - 64) ≠ 0 := by
      intro h'; apply h; bv_omega
    simpa [h] using e

theorem kp_off (K0 b : Addr) {R j : Nat} (hk : K0 = b + BitVec.ofNat 64 (1920 - 64 * R)) :
    K0 + BitVec.ofNat 64 (64 * j) = b + BitVec.ofNat 64 (1920 - 64 * R + 64 * j) := by
  rw [hk, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ark_frame {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hoth : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r)
    (hfr : Frame [slotRegion arkCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, arkCfg, Region.Contains] at ha⟩)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * m))
    (hm : m + 1 < R) (hbs : BsRel (Q s) T) :
    WP isa (.block roundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (m + 1)) ∧
      BsRel (Q s') (fun b => rnd w (m + 1) (T b)) ∧
      AArch64.eval (.nonzero .x t0) s' = some (!decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_step] at hk₁
  have hbs₁ : BsRel (Q s₁) T := by
    have : Q s₁ = Q s := funext hq₁
    rw [this]; exact hbs
  refine layer_wp (sbox_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine layer_wp (shiftRows_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine layer_wp (mixColumns_ok (hc₃.linOk hp.scr)) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (m + 1)) := by rw [hk₄, hk₃, hk₂, hk₁]
  have hok : Ok arkCfg s₄ := ark_cfg_ok (b := s₀.gpr sb) (by rw [hc₄.wr]; exact hp.scr)
    (by rw [hk₄', kp_off _ _ hp.k0]) (by omega)
  have hkey : KeyRel (keyWord s₄) (roundKey w (m + 1)) := by
    have := hp.keysAt hc₄ (m + 1) (by omega)
    unfold keyWord; rw [hk₄']; exact this
  obtain ⟨s₅, hs₅, h₅, hrd, hwr, hsp, hoth, hfr⟩ := addRoundKey_ok hok
  have hc₅ : Ctx s₀ s₅ := ark_frame hc₄ hrd hwr hsp hoth hfr
  have hbs₅ := bs_addRoundKey h₅ hbs₄ hkey
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  refine cmpLast_wp hc₅ fun s₆ hc₆ hk₆ hq₆ ht₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hoth kp (by decide), hk₄']
  · have : Q s₆ = Q s₅ := funext hq₆
    rw [this]; exact hbs₅
  · simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, ht₆]
    rw [hoth kp (by decide), hk₄', hoth sb (by decide), hc₄.base, kp_off _ _ hp.k0, t0_last _ hR hm]

/-- `mov kp, x0`. -/
theorem movKp_wp {s₀ s : State} {P : State → Prop} (hc : Ctx s₀ s)
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr .x0 → (∀ i, Q s' i = Q s i) → P s') :
    WP isa (.block [movR kp .x0]) s P := by
  refine WP.of_runBlock ⟨_, by rw [movR, runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], h _ ?_ ?_ ?_⟩
  · exact hc.step rfl rfl rfl (fun r _ hr => by simp [State.write, hr]) (Frame.refl _ _)
  · simp [State.write, State.read]
  · intro i; simp [Q, State.write, q_ne_kp i]

theorem ark_step {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * j))
    (hj : j ≤ R) (hbs : BsRel (Q s) T) {P : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → BsRel (Q s') (fun b => addRoundKey (T b) (roundKey w j)) →
      P s') : WP isa (.block addRoundKey) s P := by
  have hok : Ok arkCfg s := ark_cfg_ok (b := s₀.gpr sb) (by rw [hc.wr]; exact hp.scr)
    (by rw [hk, kp_off _ _ hp.k0]) (by rcases hp.rounds with h | h | h <;> omega)
  have hkey : KeyRel (keyWord s) (roundKey w j) := by
    have := hp.keysAt hc j hj
    unfold keyWord; rw [hk]; exact this
  obtain ⟨s', hs', h', hrd, hwr, hsp, hoth, hfr⟩ := addRoundKey_ok hok
  exact WP.of_runBlock ⟨s', hs', h s' (ark_frame hc hrd hwr hsp hoth hfr) (hoth kp (by decide))
    (bs_addRoundKey h' hbs hkey)⟩

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Four blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt4_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (Q s₀) S) :
    WP isa encrypt4 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => cipher R w (S b)) := by
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * m) ∧ BsRel (Q s) (fun b => midRounds w m (A b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * (R - 1)) ∧
    BsRel (Q s) (fun b => midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok ((Ctx.refl s₀).linOk hp.scr)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine movKp_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (Q s₂) S := by
      have : Q s₂ = Q s₁ := funext hq₂
      rw [this]; exact hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .x0 + BitVec.ofNat 64 (64 * 0) := by
      rw [hk₂, hc₁.keep _ x0_not.1 x0_not.2]; simp
    exact ark_step hp hc₂ hk₂' (by omega) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [hlast]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨hz.trans (by simp [hlast]), R - 1 - (m + 1), by omega, m + 1, rfl, by omega, hc',
        hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, kp_step, show R - 1 + 1 = R by omega] at hk₁
    have hbs₁ : BsRel (Q s₁) (fun b => midRounds w (R - 1) (A b)) := by
      have : Q s₁ = Q s := funext hq₁
      rw [this]; exact hbs
    refine layer_wp (sbox_ok (hc₁.linOk hp.scr)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine layer_wp (shiftRows_ok (hc₂.linOk hp.scr)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok (hc₄.linOk hp.scr)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [cipher_eq]; rfl

end VG.Proof.Aes.AArch64
