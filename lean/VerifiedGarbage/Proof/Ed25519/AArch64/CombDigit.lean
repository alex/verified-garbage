import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.Canonical64

/-!
# The comb's digits, signs and masks

Untrusted. Step `c` reads the nibble `combIdx c` of the scalar from its
bits, expanded one per byte at byte 768 of the workspace, by Horner's rule;
`combSign` turns it into the magnitude `|n - 8|` and the mask of its sign;
`combMasks` sets the register `maskReg k` to all ones exactly if the
magnitude is `k`, for `k = 1 … 8`, and `x22` to `1` exactly if it is `0`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

/-! ## The bit index -/

private theorem index_fact : ∀ c < 64,
    (BitVec.ofNat 64 c >>> 5 == 0) = decide (c < 32) ∧
    BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) ∧
    (c < 32 → BitVec.ofNat 64 (8 * c) + BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * combIdx c)) ∧
    (¬ c < 32 → BitVec.ofNat 64 (8 * c) - BitVec.ofNat 64 256 = BitVec.ofNat 64 (4 * combIdx c)) := by
  decide +kernel

theorem combIndex_ok (s : State) {base : Addr} (hs : Scr s base) {c : Nat} (hc : c < 64)
    (hb : s.gpr .x19 = BitVec.ofNat 64 c) :
    WP isa combIndex s fun t => t.gpr .x8 = off base (4 * combIdx c) ∧ Keeps [.x2, .x8] s t := by
  obtain ⟨hz, hl, h1, h2⟩ := index_fact c hc
  rw [combIndex]
  refine WP.seq (WP.mono (show WP isa (.block [.lsr .x .x8 .x19 5, .lsl .x .x2 .x19 3]) s fun t =>
      (t.gpr .x8 == 0) = decide (c < 32) ∧ t.gpr .x2 = BitVec.ofNat 64 (8 * c) ∧
        Keeps [.x2, .x8] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show (5 : Nat) < Size.x.bits from by decide, show (3 : Nat) < Size.x.bits from by decide,
      ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, hb, hz, hl, ite_false, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]) fun a ⟨az, a2, ka⟩ => ?_)
  refine WP.seq (WP.mono (show WP isa (.ite (.zero .x .x8) (.block [.addImm .x .x2 .x2 4])
      (.block [.subImm .x .x2 .x2 256])) a fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (4 * combIdx c) ∧ Keeps [.x2] a t by
    refine WP.ite (decide (c < 32)) (by simp only [eval, read_x, az]) (fun h => ?_) (fun h => ?_)
    · have h' := of_decide_eq_true h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 4 < 4096 by decide),
        read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, a2, h1 h', Option.some.injEq,
        exists_eq_left']
      exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
    · have h' := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil,
        exec_subImm_x (show 256 < 4096 by decide), read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq,
        a2, h2 h', Option.some.injEq, exists_eq_left']
      exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩)
    fun b ⟨b2, kb⟩ => ?_)
  have b0 : b.gpr .x0 = base := by rw [kb.gpr _ (by decide), ka.gpr _ (by decide), hs.x0]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, b0, b2, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, kb.gpr _ (by simpa using hr.1), ka.gpr _ (by simp [hr.1, hr.2])]
  · rw [RegUpd.mem_write, kb.mem, ka.mem]
  · rw [RegUpd.rd_write, kb.rd, ka.rd]
  · rw [RegUpd.wr_write, kb.wr, ka.wr]
  · rw [RegUpd.sp_write, kb.sp, ka.sp]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem combNibble_ok {s : State} {base : Addr} (hs : Scr s base) {S i : Nat} (hi : i < 64)
    (hp : s.gpr .x8 = off base (4 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combNibble) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib S i) ∧ Keeps [.x2, .x3] s t := by
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : ∀ j, off base (4 * i) + BitVec.ofNat 64 (768 + j) = off base (768 + (4 * i + j)) :=
    fun j => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (off base) (by omega)
  have hv : ∀ j < 4, ((s.mem (off base (768 + (4 * i + j)))).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (4 * i + j)) % 2) := fun j hj => by
    rw [hb _ (by omega)]; exact bit_ext _ (Nat.mod_lt _ (by decide))
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [combNibble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, hp, e0, e1, e2, e3,
    r0, r1, r2, r3, read_byte, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [nib_bits]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Sign and magnitude -/

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^
        (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) ∧
    ((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63 =
      mask (decide (n < 8)) := by
  decide +kernel

theorem combSign_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x1 = mask (decide (n < 8)) ∧
      Keeps [.x1, .x2, .x3, .x9] s t := by
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 32 from by decide, Nat.mul_zero, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, (sign_fact n hn).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The masks -/

/-- The bit of `|d| = 0`. -/
def zeroBit (a : Nat) : BitVec 64 := if a = 0 then 1 else 0

private theorem less_fact : ∀ a < 9, ∀ k < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 1)) >>> 63 -
      (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 2)) >>> 63 = mask (decide (a = k + 1)) := by
  decide +kernel

private theorem last_fact : ∀ a < 9,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 8) >>> 63 - BitVec.ofNat 64 1 = mask (decide (a = 8)) ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = zeroBit a := by
  decide +kernel

theorem combMasks_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block combMasks) s fun t =>
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (maskReg k) = mask (decide (a = k))) ∧ t.gpr .x22 = zeroBit a ∧
      Keeps [.x9, .x22, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21] s t := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [combMasks, combLess, combDiff, maskReg, combMaskRegs, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.add_sub_cancel,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk1 hk8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hk : k < 8 := by omega
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_sub_cancel, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2, ite_false]

/-! ## The table index -/

private theorem mod32_fact : ∀ c < 64,
    (BitVec.ofNat 64 c <<< 59) >>> 59 = BitVec.ofNat 64 (c % 32) := by decide +kernel

theorem combTableIdx_ok (s : State) {c : Nat} (hc : c < 64) (hb : s.gpr .x19 = BitVec.ofNat 64 c) :
    WP isa (.block [.lsl .x .x8 .x19 59, .lsr .x .x8 .x8 59]) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (c % 32) ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (59 : Nat) < Size.x.bits from by decide, ite_true, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, hb, mod32_fact c hc, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  have h : r ≠ .x8 := by simpa using hr
  rw [RegUpd.gpr_write_of_ne _ _ _ h, RegUpd.gpr_write_of_ne _ _ _ h]

end VG.Proof.Ed25519.AArch64
