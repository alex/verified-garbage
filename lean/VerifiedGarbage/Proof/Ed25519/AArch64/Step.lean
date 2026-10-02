import VerifiedGarbage.Impl.Ed25519.AArch64.Word
import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Short symbolic executions for four-word A64 arithmetic. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure Keeps (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : Keeps rs s t) (k : Keeps rs t u) :
    Keeps rs s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : Keeps rs s t)
    (inc : ∀ r ∈ rs, r ∈ rs') : Keeps rs' s t :=
  ⟨fun r hr => h.gpr r (fun hmem => hr (inc r hmem)), h.mem, h.rd, h.wr, h.sp⟩

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

theorem mulStep_ok (s : State) {t c ai b : Reg} (hz : s.gpr .x10 = 0)
    (ht8 : t ≠ .x8) (ht2 : t ≠ .x2) (ht10 : t ≠ .x10)
    (hc8 : c ≠ .x8) (hc2 : c ≠ .x2)
    (ha8 : ai ≠ .x8) (hb8 : b ≠ .x8) (htc : t ≠ c) :
    WP isa (.block (mulStep t c ai b)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * (s.gpr b).toNat ∧
      Keeps [t, c, .x8, .x2] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    ht8, ht2, hc8, hc2, ha8, hb8, Ne.symm ht2, Ne.symm ht10, htc, Ne.symm htc,
    hz, Bool.toNat_false, Nat.add_zero, BitVec.add_zero, show (0 : Nat) < 4096 by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simpa only [Word64.addCarry, Word64.carryOut, Bool.toNat_false,
      Nat.add_zero, BitVec.add_zero] using
      Word64.multiply_accumulate (s.gpr ai) (s.gpr b) (s.gpr c) (s.gpr t)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

end VG.Proof.Ed25519.AArch64
