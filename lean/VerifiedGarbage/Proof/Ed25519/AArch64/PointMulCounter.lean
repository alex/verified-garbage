import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep

/-! The public batch counter survives field and table operations. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

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

theorem batchTest_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t :=
  WP.mono (ld_ok hs (by decide) (by decide) .x19) fun _ ⟨hv, hk⟩ => ⟨hv.trans hc, hk⟩

end VG.Proof.Ed25519.AArch64
