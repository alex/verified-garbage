import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup

/-! The message length is 32 bits; the SHA-512 byte count is a 64-bit pair. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def countHigh (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (BitVec.ofBool (decide (2 ^ 32 ≤ x.toNat + (BitVec.ofNat 32 n).toNat))).setWidth 32

theorem count_pair (x : BitVec 32) (n : Nat) (hn : n < 2 ^ 32) :
    countHigh x n ++ (x + BitVec.ofNat 32 n) = BitVec.ofNat 64 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (x + BitVec.ofNat 32 n).isLt,
    Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [countHigh, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases h : 2 ^ 32 ≤ x.toNat + n
  · simp only [h, decide_true, BitVec.ofBool_true]
    change 1 * 2 ^ 32 + (x.toNat + n) % 2 ^ 32 = (x.toNat + n) % 2 ^ 64
    omega
  · simp only [h, decide_false, BitVec.ofBool_false]
    change 0 * 2 ^ 32 + (x.toNat + n) % 2 ^ 32 = (x.toNat + n) % 2 ^ 64
    omega

theorem countArgs_run {s : State} {E : BitVec 32} {index n : Nat}
    (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (260 + 4 * index)) 4)
    (hw1 : InRegions s.wr (addr E 4) 4) (hw2 : InRegions s.wr (addr E 8) 4) :
    WP isa (.block (countArgs index n)) s fun t => t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.mem = (s.mem.writeW (addr E 4)
        (s.mem.readW (addr E (260 + 4 * index)) 32 + BitVec.ofNat 32 n)).writeW (addr E 8)
        (countHigh (s.mem.readW (addr E (260 + 4 * index)) 32) n) := by
  apply WP.of_runBlock
  simp only [countArgs, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load32, State.store32, ea_mk, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, reduceCtorEq, ite_true, ite_false,
    he, hr, hw1, hw2, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, fun r h1 h2 => by simp only [h1, h2, ite_false], ?_⟩
  apply congrArg (fun v => (s.mem.writeW (addr E 4)
    (s.mem.readW (addr E (260 + 4 * index)) 32 + BitVec.ofNat 32 n)).writeW (addr E 8) v)
  change (0#32) + countHigh (s.mem.readW (addr E (260 + 4 * index)) 32) n = _
  exact BitVec.zero_add _

theorem Ctx.count {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : Ctx E g m₀ rd wr s) {index n : Nat}
    (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (addr E (260 + 4 * index)) 4)
    {x : BitVec 32} (hx : s.mem.readW (addr E (260 + 4 * index)) 32 = x) :
    WP isa (.block (countArgs index n)) s fun t => Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64 + 4, 8⟩] s.mem t.mem ∧
      t.mem.readW (E.setWidth 64 + 4) 32 = x + BitVec.ofNat 32 n ∧
      t.mem.readW (E.setWidth 64 + 8) 32 = countHigh x n := by
  have hw : FR E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (countArgs_run hc.esp hr (frame_word hf hw (by decide))
    (frame_word hf hw (by decide))) fun t ⟨htd, htw, htg, htm⟩ => ?_
  rw [hx, addr_eq (x := E) (k := 4) (by omega_using [hf]),
    addr_eq (x := E) (k := 8) (by omega_using [hf])] at htm
  change t.mem = (s.mem.writeW (E.setWidth 64 + (4 : BitVec 64)) (x + BitVec.ofNat 32 n)).writeW (E.setWidth 64 + (8 : BitVec 64)) (countHigh x n) at htm
  have hfr : Frame [⟨E.setWidth 64 + 4, 8⟩] s.mem t.mem := by
    rw [htm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simp [Region.Contains])).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 4) (k := 8) (d := 8) (n := 4) (by decide) (by decide) (by decide))
  refine ⟨hc.of_frame htd htw (htg _ (by decide) (by decide)) ?_ hfr ?_, hfr, ?_, ?_⟩
  · intro r hr _
    apply htg
    · rintro rfl; simp [calleeSaved] at hr
    · rintro rfl; simp [calleeSaved] at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Offset.sub_base _ (d := 4) (by decide))
  · rw [htm, Mem.readW_writeW_sep (w := 32) (w' := 32) (a := E.setWidth 64 + 4) (b := E.setWidth 64 + 8)
      (Offset.sep _ (d := 4) (n := 4) (e := 8) (k := 4) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [htm, Mem.readW_writeW_self32]

end VG.Proof.Ed25519.X86.Whole
