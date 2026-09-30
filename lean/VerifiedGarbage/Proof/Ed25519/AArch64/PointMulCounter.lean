import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul
import VerifiedGarbage.Proof.Ed25519.AArch64.PointBatch

/-! Untrusted: the public batch counter survives field and table operations. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem tableFrame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : 64 ≤ o) (hn : 768 ≤ o + n) :
    Outside base 64 (o + n - 64) m m' := by
  intro p hp
  exact h p (by omega) (by omega)

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 j := by
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  change s.mem.read (off base 56) 8 = _ at hc
  apply WP.of_runBlock
  simp only [batchBegin, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    addr, Size.bytes, Size.bits, State.load, State.store,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    hs.x0, hr, hw, hc, he, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ?_, fun r hr => ?_, True.intro, True.intro, rfl, ?_⟩
  · rw [write64_eq_writeW]; exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · rw [write64_eq_writeW]; exact writeW_outside _ _ _ (by decide)

theorem batchBitOffset_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchBitOffset) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 (16 * j) ∧ Keeps [.x8, .x1] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  change s.mem.read (off base 56) 8 = _ at hc
  have hshift : (BitVec.ofNat 64 j) <<< 4 = BitVec.ofNat 64 (16 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 4 = 16 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 16 * j < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [batchBitOffset, ld, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    addr, Size.bytes, State.load, RegUpd.gpr_write, BitVec.setWidth_eq,
    hs.x0, hr, hc, hshift, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    show (4 : Nat) < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem batchTest_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t :=
  WP.mono (ld_ok hs (by decide) (by decide) .x19) fun _ ⟨hv, hk⟩ => ⟨hv.trans hc, hk⟩

end VG.Proof.Ed25519.AArch64
