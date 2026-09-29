import VerifiedGarbage.Proof.Sha3.Arm.Permute
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Impl.Sha3.Arm.Stream

/-!
# SHA-3 on ARMv7: calling the permutation, and saving registers

Untrusted: everything here is checked by Lean. What the streaming functions
(`VG.Impl.Sha3.Arm.Stream`) share: the call of the permutation, the saving
and restoring of our caller's registers in the scratch space, and
arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha512.Arm (A A_eq contains_A)
open VG.Proof.Sha3 (off_disjoint sub_offset add_zero')

/-! ## The permutation -/

theorem permute_noCalls : permute.noCalls = true := by decide +kernel

theorem permute_r0 : ∀ i ∈ instrs permute, dstOf i ≠ some .r0 := by
  have : ((instrs permute).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem permute_r1 : ∀ i ∈ instrs permute, dstOf i ≠ some .r1 := by
  have : ((instrs permute).all fun i => dstOf i != some .r1) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The state and the permutation's part of a scratch space of `N` bytes. -/
theorem covers_of {wr : List Region} {st scr : BitVec 32} {N : Nat} (hN : 512 ≤ N)
    (hS : regR st 200 ∈ wr) (hC : regR scr N ∈ wr) : Covers [regR st 200, regR scr 512] wr := by
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, hS, 0, by simp, by simp⟩
  · exact ⟨_, hC, 0, by simp, by simpa using hN⟩

/-- Calling `vg_keccak_f1600` on the state at `r0`, with scratch space at
`r1`: the callee-saved registers other than `lr`, and `r0` and `r1`, are
kept. -/
theorem call_ok {s : State} {st scr : BitVec 32} (h0 : s.gpr .r0 = st) (h1 : s.gpr .r1 = scr)
    (fS : st.toNat + 200 ≤ 2 ^ 32) (fC : scr.toNat + 512 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint (regR st 200) (regR scr 512))
    (hw : Covers [regR st 200, regR scr 512] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR st 200, regR scr 512] s.mem s'.mem →
      stateAt s'.mem (State.addr st) = keccakF (stateAt s.mem (State.addr st)) → Q s') :
    WP isa Impl.Sha3.Arm.Stream.permuteCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.call (k := Proof.Sha3.permuteArm) permute_verified.1
    (rd := []) (wr := [regR st 200, regR scr 512]) ?_ ?_ hw ?_ permute_noCalls
  · simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, d₁, fS, fC⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs (by rw [hg _ permute_r0 (by decide), h0])
      (by rw [hg _ permute_r1 (by decide), h1]) hf (by rw [hpost]; rfl)

/-! ## Saving the caller's registers -/

/-- The caller's registers `g` saved at `scr`. -/
def SSaved (scr : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ p ∈ Impl.Sha3.Arm.Stream.saved, m.readW (A scr p.2) 32 = g p.1

theorem ssaved_ok : ∀ p ∈ Impl.Sha3.Arm.Stream.saved,
    p.1 ≠ .r1 ∧ p.1 ≠ .r12 ∧ p.2 < 4096 ∧ 512 ≤ p.2 ∧ p.2 + 4 ≤ 532 := by decide

set_option simprocs false in
theorem saveMemA_ssaved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 640 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    SSaved b g (saveMemA m b g Impl.Sha3.Arm.Stream.saved) := by
  intro p hp
  simp only [Impl.Sha3.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [Impl.Sha3.Arm.Stream.saved, saveMemA, Mem.readW_writeW_self32,
    readW_writeW_A (hfit := hfit)]

theorem SSaved.keep {scr : BitVec 32} {g : Reg → BitVec 32} {m m' : Mem} (h : SSaved scr g m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 532 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) :
    SSaved scr g m' := fun p hp => by
  obtain ⟨-, -, -, h1, h2⟩ := ssaved_ok p hp
  rw [hk _ h1 h2]; exact h p hp

theorem SSaved.of_gpr {scr : BitVec 32} {g g' : Reg → BitVec 32} {m : Mem} (h : SSaved scr g m)
    (hg : ∀ r, r ≠ .r12 → g r = g' r) : SSaved scr g' m := fun p hp => by
  rw [h p hp, hg _ (ssaved_ok p hp).2.1]

/-- Writes to the state and to the permutation's scratch space keep the
words of the scratch space after the permutation's part. -/
theorem readW_hi {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) {d : Nat}
    (hd₁ : 512 ≤ d) (hd₂ : d + 4 ≤ 640) : m'.readW (A scr d) 32 = m.readW (A scr d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hrs r hr with rfl | rfl
  · refine hd.symm.sub_left ?_
    rw [A_eq (by omega)]; exact sub_offset (by omega) (by omega)
  · have := off_disjoint (State.addr scr) (a := d) (n := 4) (b := 0) (k := 512) (by omega)
      (by omega) (.inr hd₁)
    rw [add_zero'] at this
    rw [A_eq (by omega)]; exact this

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem SSaved.frame {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {g : Reg → BitVec 32} {m m' : Mem}
    (h : SSaved scr g m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) : SSaved scr g m' :=
  h.keep fun _ hd₁ hd₂ => readW_hi fC hd hf hrs hd₁ (by omega)

theorem restore_eq :
    Impl.Sha3.Arm.Stream.restore = Impl.Sha3.Arm.Stream.saved.map (fun p => Instr.ldr p.1 .r1 p.2) := rfl

theorem save_eq :
    Impl.Sha3.Arm.Stream.save = Impl.Sha3.Arm.Stream.saved.map (fun p => Instr.str p.1 .r12 p.2) := rfl

/-- Every callee-saved register is saved, or one of `r8`–`r11`. -/
theorem preserved_cases : ∀ r ∈ preserved,
    (∃ p ∈ Impl.Sha3.Arm.Stream.saved, p.1 = r) ∨ r ∈ [Reg.r8, .r9, .r10, .r11] := by decide

/-! ## Arithmetic on 32-bit values -/

theorem ofNat32_succ (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) :=
  VG.Proof.MdStream.Arm.sub_ofNat h

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) :=
  VG.Proof.MdStream.Arm.ofNat_beq_zero h

theorem sub_beq_zero32 {a : Nat} (ha : a < 2 ^ 32) (y : BitVec 32) :
    (BitVec.ofNat 32 a - y == 0) = decide (a = y.toNat) := by
  by_cases h : a = y.toNat
  · subst h; simp
  · have : BitVec.ofNat 32 a - y ≠ 0 := by intro e; apply h; bv_omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem beq_zero32 (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h]; simp [this]

theorem xor_setWidth32 (x y : Byte) : (x.setWidth 32 ^^^ y.setWidth 32).setWidth 8 = x ^^^ y := by
  ext i hi
  simp

theorem xor_setWidth32' (x : Byte) (y : BitVec 32) :
    (x.setWidth 32 ^^^ y).setWidth 8 = x ^^^ y.setWidth 8 := by
  ext i hi
  simp

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem add_imm0 (a : BitVec 32) : a + 0 = a := by simp

theorem sub_imm0 (a : BitVec 32) : a - 0 = a := by simp

/-! ## The arguments on the stack -/

theorem arg_in {s : State} {n : Nat} (hsp : s.sp.toNat + 4 * n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    (⟨stackArgAddr s 0, 4 * n⟩ : Region).Contains (stackArgAddr s k) 4 := by
  simp only [stackArgAddr, Region.Contains]
  rw [addr_add (a := s.sp) (k := 4 * k) (by omega), addr_add (a := s.sp) (k := 4 * 0) (by omega)]
  bv_omega

theorem argByte_eq {s : State} {n : Nat} (hsp : s.sp.toNat + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (a := s.sp) (k := 4 * (k / 4)) (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha3.Arm
