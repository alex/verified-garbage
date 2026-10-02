import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.Ladder

/-!
# X448 on x86 (32-bit): reading a scalar bit

Only the public loop counter selects an address; the bit affects an XOR mask.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def stepPre : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi),
    .movzx8 .eax (at_ .ebp BITS), ld .ecx SWAP, .alu .xor .ecx (.reg .eax), st .eax SWAP,
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ (BitVec.ofNat 8 b).setWidth 32) =
      mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .esi = BitVec.ofNat 32 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 32 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .esi = BitVec.ofNat 32 t ∧ s'.gpr .ebx = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.esi, .eax, .ecx, .ebx, .ebp] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 32 kt) := by
  have hb' : s.gpr .esi - (1 : BitVec 32) = BitVec.ofNat 32 t := by
    change s.gpr .esi - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin := hs.read (d := BITS + t) (n := 1) (by simp only [BITS]; omega)
  have hr := hs.read (d := SWAP) (n := 4) (by decide)
  have hw := hs.write (d := SWAP) (n := 4) (by decide)
  have ba : (s.gpr .edi + BitVec.ofNat 32 t + BitVec.ofNat 32 BITS).setWidth 64 = off base (BITS + t) := by
    rw [Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by simp only [BITS]; omega)
  have sa := hs.ea (d := SWAP) (by decide)
  simp only [State.ea, sc, at_] at sa
  apply WP.of_runBlock
  simp only [stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    State.ea, sc, at_, hb', ba, sa, State.load8, State.load32, State.store32, hin, hr, hw, hbit,
    hswap, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have ek : (BitVec.ofNat 8 kt).setWidth 32 = BitVec.ofNat 32 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial, by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.X86
