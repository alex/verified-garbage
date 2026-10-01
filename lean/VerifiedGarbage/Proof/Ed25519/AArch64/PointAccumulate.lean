import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! Untrusted: the scalar bit mask and the selection of the saved point. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem scalarBitMask_ok {s : State} {base : Addr} (hs : Scr s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .x19 = BitVec.ofNat 64 j) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitMask) s fun t =>
      t.gpr .x3 = mask (decide (bit = 0)) ∧ Keeps [.x8, .x3] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) + BitVec.ofNat 64 768 =
      off base (768 + (start + j)) := by
    rw [← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hm : ((BitVec.ofNat 8 bit).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 = mask (decide (bit = 0)) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitMask, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    show (1 : Nat) < 4096 from by decide, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT,
    and_self, hj, hstart, hs.x0, he, hr, read_byte, hb, hm,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem savedPoint_congr (e f : Env) (h : ∀ i : Slot, 16 ≤ i.val → e i = f i) :
    point e 17 18 19 20 = point f 17 18 19 20 := by
  simp only [point, h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide)]

theorem Keep.bit {base : Addr} {s t : State} (h : Keep base s t) (i : Nat) (hi : i < 512) :
    t.mem (off base (768 + i)) = s.mem (off base (768 + i)) :=
  h.mem _ (by rw [ofs_off' base (by omega)]; omega)

end VG.Proof.Ed25519.AArch64
