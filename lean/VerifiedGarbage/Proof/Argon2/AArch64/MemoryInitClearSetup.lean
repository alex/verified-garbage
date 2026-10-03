import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitScale
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitSpace
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLayout
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClear

/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  count : t.gpr .x8 = wordAt s blocksOffset
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa (.block clearHeader) s (ClearHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hb : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240#64) 8 := blocksRead
  apply WP.of_runBlock
  simp only [clearHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset, blocksOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hb, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _ _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure ClearSetup (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  count : t.gpr .x8 = wordAt s blocksOffset * 128
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearSetup_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa clearSetupCode s (ClearSetup s) := by
  unfold clearSetupCode clearSetup
  rw [WP.block_append_iff]
  refine (clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .x8 7).mono ?_
  intro b hb
  exact ⟨(hb.other _ (by decide) (by decide)).trans ha.destination,
    by rw [hb.value, ha.count]; rfl,
    (hb.other _ (by decide) (by decide)).trans ha.zero,
    fun r h1 h2 h3 h4 h5 => (hb.other r h2 h5).trans (ha.other r h1 h2 h3 h4 h5),
    hb.mem.trans ha.mem, hb.rd.trans ha.rd, hb.wr.trans ha.wr, hb.sp.trans ha.sp⟩

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .x22 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => Cleared s t memory blocks := by
  unfold clear
  refine WP.seq ((clearSetup_ok s memoryRead blocksRead).mono ?_)
  intro b hb
  have count : b.gpr .x8 = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.count, blocksWord, show (128 : Addr) = BitVec.ofNat 64 128 from rfl,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .x22 = memory := hb.destination.trans memoryWord
  have zero := hb.zero
  have mem := hb.mem
  have rd := hb.rd
  have wr := hb.wr
  have other := hb.other
  have sp := hb.sp
  refine (clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 h4 h5 => (ht.other r h2 h1 h4 h5).trans (other r h1 h2 h3 h4 h5), ?_,
      ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.AArch64.MemoryInit
