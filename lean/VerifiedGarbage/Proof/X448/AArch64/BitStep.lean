import VerifiedGarbage.Proof.X448.AArch64.Ops
import VerifiedGarbage.Proof.X448.Ladder

/-!
# X448 on AArch64: reading a scalar bit

Untrusted: everything here is checked by Lean. The public counter selects a
byte of the scalar-bit array. Only the XOR mask, never control flow, depends
on that bit and the previous swap bit.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS,
    ld .x5 SWAP, .logic .eor .x .x5 .x5 .x4, st .x4 SWAP,
    .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 t ∧ s'.gpr .x6 = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.x19, .x4, .x5, .x6, .x11] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 t := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have enc : BITS % 1 = 0 ∧ BITS < 4096 * 1 := by decide
  have encSwap : SWAP % 8 = 0 ∧ SWAP < 4096 * 8 := by decide
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  apply WP.of_runBlock
  simp only [stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, hb', hs.x3, addr, enc, encSwap, and_self,
    off, Offset.add_add, Nat.add_comm t BITS, State.load, State.store,
    hin, hr, hw, read1_eq, read8_eq, write8_eq, hbit, hswap',
    Option.bind_some, Option.map_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  have ext : (BitVec.setWidth 32 (BitVec.ofNat 8 kt)).setWidth 64 =
      (BitVec.ofNat 8 kt).setWidth 64 := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  simp only [ext]
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.AArch64
