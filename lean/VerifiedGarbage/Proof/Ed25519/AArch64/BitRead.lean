import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte

/-! Load the next scalar byte and calculate its bit-output address. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

theorem scalarByteRead_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i : Nat) (hi : i < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block [.add .x .x8 .x1 .x19, .ldrb .x8 .x8 0,
      .lsl .x .x9 .x19 3, .add .x .x9 .x0 .x9]) s fun t =>
      t.gpr .x8 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x9 = off base (8 * i) ∧
      Keeps [.x8, .x9] s t := by
  have hshift : (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (0 : Nat) < 4096 * 1 from by decide, show (0 : Nat) % 1 = 0 from rfl,
    show (3 : Nat) < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, hc, hs.x0, hshift, BitVec.add_zero, BitVec.setWidth_eq, hr, read_byte,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.setWidth_setWidth (by decide), True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

end VG.Proof.Ed25519.AArch64
