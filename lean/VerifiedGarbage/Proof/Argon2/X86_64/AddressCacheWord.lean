import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMeta

/-! Read exactly the public indexed word of the cached address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wordAddress (s : State) : Addr :=
  s.gpr .rcx + s.gpr .rax * BitVec.ofNat 64 8 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .rdi = s.mem.readW (wordAddress s) 64 ∧
      Divide.Keeps [.rdi] s t := by
  dsimp only [wordAddress] at hr
  apply WP.of_runBlock
  simp only [wordRead, wordAddress, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, State.ea, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .rcx = AddressCalls.work s)
    (index : a.gpr .rax = s.gpr .r15 &&& 127) :
    wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .r15).toNat % 128)) := by
  unfold wordAddress off
  rw [scratch, index, index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change AddressCalls.work s + BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)) +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)))
    (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.X86_64.AddressCache.word s fun t => t.gpr .rdi =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.rcx, .rax, .rdi] s t := by
  unfold Impl.Argon2.X86_64.AddressCache.word
  refine WP.seq ((wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .r15).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .r15).toNat (by decide : 0 < 128); omega) (by omega)⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.X86_64.AddressCache
