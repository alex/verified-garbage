import VerifiedGarbage.Proof.X448.Arm.Ops
import VerifiedGarbage.Proof.X448.Ladder

/-!
# X448 on ARMv7: reading a scalar bit

Untrusted: everything here is checked by Lean. Only the public loop
counter selects an address; the bit affects an XOR mask.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def stepPre : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS,
    ld .r2 SWAP, .dp .eor .r2 .r2 (.reg .r3), st .r3 SWAP,
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ (BitVec.ofNat 8 b).setWidth 32) =
      mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .r11 = BitVec.ofNat 32 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 32 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .r11 = BitVec.ofNat 32 t ∧ s'.gpr .r5 = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.r11, .r3, .r2, .r5, .r7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 32 kt) := by
  have hb' : s.gpr .r11 - (1 : BitVec 32) = BitVec.ofNat 32 t := by
    change s.gpr .r11 - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin := hs.read (d := BITS + t) (n := 1) (by simp only [BITS]; omega)
  have hr := hs.read (d := SWAP) (n := 4) (by decide)
  have hw := hs.write (d := SWAP) (n := 4) (by decide)
  have ba : State.addr (s.gpr .r0 + BitVec.ofNat 32 t + BitVec.ofNat 32 BITS) = off base (BITS + t) := by
    rw [Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by simp only [BITS]; omega)
  have sa := hs.ea (d := SWAP) (by decide)
  have se : SWAP < 4096 := by decide
  have be : BITS < 4096 := by decide
  have enc0 : encodable (0 : BitVec 32) = true := by decide
  have enc1 : encodable (1 : BitVec 32) = true := by decide
  apply WP.of_runBlock
  simp only [stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    enc0, enc1, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hb', ba, sa, se, be, State.load8, State.load32, State.store32, hin, hr, hw, hbit,
    hswap, Option.map_some, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have ek : (BitVec.ofNat 8 kt).setWidth 32 = BitVec.ofNat 32 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial, by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.Arm
