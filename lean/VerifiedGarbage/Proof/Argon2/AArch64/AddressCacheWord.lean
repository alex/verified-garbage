import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheMeta

/-! Read exactly the public indexed word of the cached address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def wordAddress (s : State) : Addr :=
  s.gpr .x8 * BitVec.ofNat 64 8 + s.gpr .x3 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .x0 = s.mem.readW (wordAddress s) 64 ∧
      Divide.Keeps [.x0, .x12, .x13, .x15] s t := by
  change InRegions (s.rd ++ s.wr) (s.gpr .x8 * 8#64 + s.gpr .x3 + 6144#64) 8 at hr
  apply WP.of_runBlock
  simp only [wordRead, wordAddress, Instructions.mov, Instructions.add, Instructions.addi,
    Instructions.mark, Instructions.imm, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, addr, State.load,
    Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show ¬6144 < 4096 from by decide,
    show 6144 < 65536 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, and_self, Option.map_some, Option.bind_some,
    ← BitVec.mul_two, BitVec.mul_assoc,
    show (2#64) * (2#64 * 2#64) = 8#64 from rfl,
    show (6144#16).setWidth 64 = 6144#64 from rfl,
    show BitVec.ofInt 64 6144 = 6144#64 from rfl,
    hr, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .x3 = AddressCalls.work s)
    (index : a.gpr .x8 = s.gpr .x23 &&& 127) :
    wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .x23).toNat % 128)) := by
  unfold wordAddress off
  rw [scratch, index, index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)) + AddressCalls.work s +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128))) (AddressCalls.work s),
    BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)))
      (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.AArch64.AddressCache.word s fun t => t.gpr .x0 =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.x3, .x8, .x0, .x12, .x13, .x15] s t := by
  unfold Impl.Argon2.AArch64.AddressCache.word
  refine WP.seq ((wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .x23).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .x23).toNat (by decide : 0 < 128); omega) (by omega)⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.AArch64.AddressCache
