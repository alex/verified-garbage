import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearSetup

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8) :
    WP isa (.block lanesHeader) s (LanesHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184#64) 8 := lanesRead
  apply WP.of_runBlock
  simp only [lanesHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset,
    VG.Impl.Argon2.AArch64.Initial.lanesOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hl, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .x22 = memory
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = BitVec.ofNat 64 lanes
  stride : t.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .x21 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .x21 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => (ht.other r h4 h5).trans (ha.other r h1 h2 h3 h5),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  · rw [ht.other .x22 (by decide) (by decide), ha.destination, memoryWord]
  · rw [ht.other .x20 (by decide) (by decide), ha.lane]
  · rw [ht.other .x23 (by decide) (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .x21 (by decide) (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.AArch64.MemoryInit
