import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitScale
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSpace
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLayout

/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .r14 = wordAt s memoryOffset
  count : t.gpr .rax = wordAt s blocksOffset
  zero : t.gpr .rcx = 0
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8) :
    WP isa (.block clearHeader) s (ClearHeader s) := by
  apply WP.of_runBlock
  simp only [clearHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, blocksOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 240 = (240 : Addr) from rfl,
    memoryRead, blocksRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .r14 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => Cleared s t memory blocks := by
  unfold clear clearSetup
  apply WP.seq
  rw [WP.block_append_iff]
  refine (clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .rax 7).mono ?_
  intro b hb
  have count : b.gpr .rax = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.value, ha.count, blocksWord, ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .r14 = memory := (hb.other _ (by decide)).trans (ha.destination.trans memoryWord)
  have zero : b.gpr .rcx = 0 := (hb.other _ (by decide)).trans ha.zero
  have mem : b.mem = s.mem := hb.mem.trans ha.mem
  have rd : b.rd = s.rd := hb.rd.trans ha.rd
  have wr : b.wr = s.wr := hb.wr.trans ha.wr
  have other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → b.gpr r = s.gpr r :=
    fun r h1 h2 h3 => (hb.other r h2).trans (ha.other r h1 h2 h3)
  refine (clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 => (ht.other r h2 h1).trans (other r h1 h2 h3), ?_,
      ht.rd.trans rd, ht.wr.trans wr⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.X86_64.MemoryInit
