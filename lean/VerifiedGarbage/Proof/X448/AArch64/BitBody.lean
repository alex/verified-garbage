import VerifiedGarbage.Proof.X448.AArch64.BitWrite

/-!
# X448 on AArch64: one scalar byte

The public byte counter selects a scalar byte, expands it, and advances the
loop.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def bitHead : List Instr :=
  [.add .x .x11 .x1 .x19, .ldrb .x4 .x11 0,
    .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11]

def bitTail : List Instr := [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 56]

def bitRegs : List Reg := [.x4, .x5, .x19, .x11, .x8]

theorem bitHead_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hb : s.gpr .x19 = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitHead) s fun t =>
      t.gpr .x4 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x11 = off base (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x11] s t := by
  apply WP.of_runBlock
  simp only [bitHead, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, hk, hb, hs.x3,
    addr, Nat.reduceMod, Nat.reduceMul, and_self, BitVec.add_zero,
    State.load, hkr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, off]
    have := (s.mem (k + BitVec.ofNat 64 i)).isLt
    omega
  · apply congrArg (base + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    change (i % 2 ^ 64 * 8) % 2 ^ 64 = (8 * i) % 2 ^ 64
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 56) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block bitTail) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 56) ∧
      t.mem = s.mem ∧ Keeps [.x19, .x11] s t := by
  have check : ∀ n < 56,
      ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 56) == 0) = decide (n + 1 = 56) :=
    by decide +kernel
  apply WP.of_runBlock
  simp only [bitTail, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hb, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(BitVec.ofNat_add _ _).symm, check i hi, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hi : i < 56) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 56) ∧
      t.gpr .x8 = 1 ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++ bitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

end VG.Proof.X448.AArch64
