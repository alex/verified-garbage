import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-!
# The comb's digits, signs and masks

Step `j` reads the nibbles `2j + 1` and `2j` of the scalar from its bits,
expanded one per byte at byte 768 of the workspace, by Horner's rule;
`combSign` turns each into the magnitude `|n - 8|` and the mask of its sign;
`combMasks` sets the register for `k` to all ones exactly if the magnitude is
`k`, for `k = 1 … 8`, and another to `1` exactly if it is `0`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

/-! ## The bit index -/

private theorem index_fact : ∀ j < 32, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem combIndex_ok (s : State) {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 32)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x8 .x19 3, .add .x .x8 .x0 .x8] : List Instr)) s fun t =>
      t.gpr .x8 = off base (8 * j) ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (3 : Nat) < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, index_fact j hj, hs.x0, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem combNibble_ok {s : State} {base : Addr} (hs : Scr s base) {S i p o : Nat} (hi : i < 64)
    (hp : s.gpr .x8 = off base p) (hpo : p + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block (combNibble o)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib S i) ∧ Keeps [.x2, .x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : ∀ j, off base p + BitVec.ofNat 64 (o + j) = off base (768 + (4 * i + j)) :=
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
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show o + 3 < 4096 * 1 by omega, show o + 2 < 4096 * 1 by omega, show o + 1 < 4096 * 1 by omega,
    show o < 4096 * 1 by omega,
    Nat.reduceMul, and_self, hp, e0, e1, e2, e3,
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

theorem masksOdd_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (combMasks oddRegs .x22)) s fun t =>
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (oddReg k) = mask (decide (a = k))) ∧ t.gpr .x22 = zeroBit a ∧
      Keeps [.x22, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21] s t := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [combMasks, oddRegs, oddReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk1 hk8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem masksEven_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (combMasks evenRegs .x8)) s fun t =>
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (evenReg k) = mask (decide (a = k))) ∧ t.gpr .x8 = zeroBit a ∧
      Keeps [.x8, .x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24] s t := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [combMasks, evenRegs, evenReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk1 hk8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## Both digits -/

/-- What `combDigits` leaves for step `j`'s two digits. -/
structure DigitsOut (s : State) (S j : Nat) (t : State) : Prop where
  oddMask : ∀ k, 1 ≤ k → k ≤ 8 → t.gpr (oddReg k) = mask (decide (mag (nib S (2 * j + 1)) = k))
  oddZero : t.gpr .x22 = zeroBit (mag (nib S (2 * j + 1)))
  evenMask : ∀ k, 1 ≤ k → k ≤ 8 → t.gpr (evenReg k) = mask (decide (mag (nib S (2 * j)) = k))
  evenZero : t.gpr .x8 = zeroBit (mag (nib S (2 * j)))
  keeps : Keeps (clob ++ [.x1]) s t

theorem combDigits_ok {s : State} {base : Addr} (hs : Scr s base) {S j : Nat} (hj : j < 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigits) s (DigitsOut s S j) := by
  have no : nib S (2 * j + 1) < 16 := nib_lt _ _
  have ne : nib S (2 * j) < 16 := nib_lt _ _
  simp only [combDigits, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs hj hc) fun a ⟨a8, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hsa (S := S) (i := 2 * j + 1) (by omega) a8 (by omega) (by decide)
    (by rw [ka.mem]; exact hb)) fun b ⟨b2, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok b no b2) fun c ⟨c2, _, kc⟩ => ?_
  have hsc := (hsa.of_keeps kb (by decide)).of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masksOdd_ok _ (mag_lt no) c2) fun e ⟨em, ez, ke⟩ => ?_
  have e8 : e.gpr .x8 = off base (8 * j) := by
    rw [ke.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a8]
  have hse : Scr e base := hsc.of_keeps ke (by decide)
  have hbe : ∀ q < 256, e.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun q hq => by
    rw [ke.mem, kc.mem, kb.mem, ka.mem]; exact hb q hq
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hse (S := S) (i := 2 * j) (by omega) e8 (by omega) (by decide) hbe)
    fun f ⟨f2, kf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok f ne f2) fun g ⟨g2, _, kg⟩ => ?_
  refine WP.mono (masksEven_ok _ (mag_lt ne) g2) fun t ⟨tm, tz, kt⟩ => ?_
  refine ⟨fun k h1 h8 => ?_, ?_, tm, tz, ?_⟩
  · have hk : oddReg k ∉ [Reg.x8, .x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24, .x2, .x9] := by
      have : ∀ k < 9, oddReg k ∉ [Reg.x8, .x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24, .x2, .x9] := by
        decide
      exact this k (by omega)
    rw [kt.gpr _ (fun h => hk (by simp only [List.mem_cons] at h ⊢; tauto)),
      kg.gpr _ (fun h => hk (by simp only [List.mem_cons] at h ⊢; tauto)),
      kf.gpr _ (fun h => hk (by simp only [List.mem_cons] at h ⊢; tauto))]
    exact em k h1 h8
  · rw [kt.gpr _ (by decide), kg.gpr _ (by decide), kf.gpr _ (by decide)]
    exact ez
  · have K : Keeps (clob ++ [.x1]) s t := ((((((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
      (ke.mono (by decide))).trans (kf.mono (by decide))).trans (kg.mono (by decide))).trans
      (kt.mono (by decide))
    exact K

end VG.Proof.Ed25519.AArch64
