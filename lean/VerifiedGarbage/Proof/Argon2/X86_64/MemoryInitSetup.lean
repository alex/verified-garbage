import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitClearSetup

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .r14 = wordAt s memoryOffset
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8) :
    WP isa (.block lanesHeader) s (LanesHeader s) := by
  apply WP.of_runBlock
  simp only [lanesHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, VG.Impl.Argon2.X86_64.Initial.lanesOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 184 = (184 : Addr) from rfl,
    memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .r14 = memory
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = BitVec.ofNat 64 lanes
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → r ≠ .r13 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .r13 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => (ht.other r h4).trans (ha.other r h1 h2 h3),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr⟩
  · rw [ht.other .r14 (by decide), ha.destination, memoryWord]
  · rw [ht.other .r12 (by decide), ha.lane]
  · rw [ht.other .r15 (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .r13 (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.X86_64.MemoryInit
