import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.X448.X86_64.Iter

/-!
# Ed448 base-point multiplication on x86-64: one bit

`step`: the counter `rbx` counts down to the bit `t`; `R` (slots 0–2) is
doubled, `T = R + Q` computed into slots 3–5, and `T` swapped into `R` with
the mask of byte `t` of `BITS` (the bit). Only the slots, the product's
words, the counter and the registers `clob` change.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap ea_bits
  clob)
open VG.Impl.X448.X86_64 (BITS slot cswap)

theorem dec_ok (s : State) {t : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) :
    WP isa (.block ([.alu .sub .rbx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hb',
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl,
    rfl, rfl⟩

theorem mask_bit : ∀ b < 2, BitVec.setWidth 64 (0 : BitVec 32) - (BitVec.ofNat 8 b).setWidth 64 =
    mask (decide (b = 1)) := by decide

theorem bitMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block bitMask) s fun s' =>
      s'.gpr .rcx = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.rdx, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  apply WP.of_runBlock
  simp only [bitMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load8, ea_bits hs.rdi hb, hin, hbit, ite_true, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

theorem step_eq : step fld = ([.alu .sub .rbx (.imm 1)] : List Instr) ++ (fieldCode fld doubleOps ++
    (fieldCode fld addOps ++ (bitMask ++ (cswap (slot 0) (slot 3) ++ (cswap (slot 1) (slot 4) ++
    (cswap (slot 2) (slot 5) ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))))))) := by
  simp only [step, List.append_assoc]

/-- The slots after an iteration, for the bit `sw`. -/
def stepEnv (sw : Bool) (e : Env) : Env :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (evalOps addOps (evalOps doubleOps e))))

theorem test_ok (s : State) (n : Nat) (hn : n < 456) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block ([.alu .test .rbx (.reg .rbx)] : List Instr)) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have e : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    have : ∀ n < 456, (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
      decide +kernel
    exact this n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb, e]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩

include hf in
/-- An iteration, for the bit `t` (`b`). -/
theorem step_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (step fld)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Proof.X448.X86_64.Outside base 64 1584 s.mem s'.mem ∧
      E s'.mem base = stepEnv (decide (b = 1)) (E s.mem base) := by
  rw [step_eq, WP.block_append_iff]
  refine WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf doubleOps doubleOps_valid hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf addOps addOps_valid hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have b3 : s3.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide)]; exact b1
  have hofs : Proof.X448.X86_64.ofs base (off base (BITS + t)) = BITS + t :=
    Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)
  have hout : Proof.X448.X86_64.ofs base (off base (BITS + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (BITS + t)) :=
    Or.inr (by rw [hofs]; simp only [BITS]; omega)
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b := by
    rw [k3.mem _ hout, k2.mem _ hout, m1, hbit]
  rw [WP.block_append_iff]
  refine WP.mono (bitMask_ok hs3 ht b3 hb2 hbit3) fun s4 ⟨c4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs4 0 3 (by decide) c4) fun s5 ⟨k5, c5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs5 1 4 (by decide) (c5.trans c4)) fun s6 ⟨k6, c6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs6 2 5 (by decide) (c6.trans (c5.trans c4))) fun s7 ⟨k7, _, e7⟩ => ?_
  have b7 : s7.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), g4 _ (by decide)]
    exact b3
  refine WP.mono (test_ok s7 t ht b7) fun s' ⟨z', g', m', rd', wr'⟩ => ?_
  refine ⟨(g' _).trans b7, z', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [g', k7.gpr r hr.2, k6.gpr r hr.2, k5.gpr r hr.2, g4 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr.2 (h ▸ by decide), fun h => hr.2 (h ▸ by decide)⟩),
      k3.gpr r hr.2, k2.gpr r hr.2, g1 r hr.1]
  · rw [rd', k7.rd, k6.rd, k5.rd, rd4, k3.rd, k2.rd, rd1]
  · rw [wr', k7.wr, k6.wr, k5.wr, wr4, k3.wr, k2.wr, wr1]
  · rw [m', ← m1]
    exact ((k2.mem.trans k3.mem).trans (by rw [m4]; exact Proof.X448.X86_64.Outside.refl _ _ _ _)).trans
      ((k5.mem.trans k6.mem).trans k7.mem)
  · rw [m', e7, e6, e5, m4, e3, e2, m1]
    rfl

end VG.Proof.Ed448.X86_64
