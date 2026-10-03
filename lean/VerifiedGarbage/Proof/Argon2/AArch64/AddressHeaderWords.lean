import VerifiedGarbage.Impl.Argon2.AArch64.AddressHeader
import VerifiedGarbage.Proof.Argon2.AArch64.BlockStore
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! Short independent-address input header writes. -/

namespace VG.Proof.Argon2.AArch64.AddressHeader

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressHeader

theorem registerWord_ok (s : State) (i : Nat) (r : Reg)
    (hi : i < 128)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (registerWord i r)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i)) (s.gpr r) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega
  apply WP.of_runBlock
  simp only [registerWord, VG.Impl.Argon2.AArch64.Instructions.store,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound, hw,
    and_self, ite_true, State.store, State.read, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem frameWord_ok (s : State) (i offset : Nat) (hi : i < 128)
    (ha : offset % 8 = 0) (hb : offset + 8 ≤ 272)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) offset) 8)
    (hw : InRegions s.wr (off (s.gpr .x0) (8 * i)) 8) :
    WP isa (.block (frameWord i offset)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x0) (8 * i))
        (s.mem.readW (off (s.gpr .x19) offset) 64) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [off] at hr hw
  have addrBound : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := by omega
  have offsetBound : offset % 8 = 0 ∧ offset < 32768 := ⟨ha, by omega⟩
  apply WP.of_runBlock
  simp only [frameWord, VG.Impl.Argon2.AArch64.Instructions.store,
    VG.Impl.Argon2.AArch64.Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, addrBound,
    offsetBound, hr, hw, and_self, ite_true, State.store, State.load, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

end VG.Proof.Argon2.AArch64.AddressHeader
