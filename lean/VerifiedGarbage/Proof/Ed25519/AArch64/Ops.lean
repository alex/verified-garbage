import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Field64
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! Merged from `Proof.Ed25519.AArch64.Carry`. -/
section
/-! Reduction of the carry above four 64-bit field limbs. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

private theorem carry38_word (c : Bool) :
    addCarry 0 0 c * 38 = BitVec.ofNat 64 (38 * c.toNat) := by
  cases c <;> decide

private theorem carry38_arith (a0 a1 a2 a3 v : Word) (hv : v.toNat < 2 ^ 58) :
    let c0 := carryOut a0 v false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let c3 := carryOut a3 0 c2
    toFe (val4 (addCarry a0 v false + addCarry 0 0 c3 * 38)
      (addCarry a1 0 c0) (addCarry a2 0 c1) (addCarry a3 0 c2)) =
      toFe (val4 a0 a1 a2 a3 + v.toNat) := by
  intro c0 c1 c2 c3
  rw [carry38_word]
  apply foldCarry_field _ _ _ _ _ (val4_lt a0 a1 a2 a3) hv
  simpa only [val4, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, show (0 : Word).toNat = 0 from rfl] using
    add4_value a0 a1 a2 a3 v 0 0 0 false

theorem carry38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hv : (s.gpr .x8).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      toFe (val4 (s'.gpr .x4) (s'.gpr .x5) (s'.gpr .x6) (s'.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + (s.gpr .x8).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp only [carry38, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := carry38_arith (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) hv
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Memory and register frames for field operations. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

def clob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x20, .x21, .x22, .x23, .x24]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base large) :
    Scr t base large := ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.fe {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : FieldRange d large) : fe t.mem base d = fe s.mem base d :=
  h.mem.fe hd (by have := hd'.2; have := workSize_le large; omega)

theorem Op.of_store {base : Addr} {o : Nat} {s t : State} (ho : FieldRange o large) (h : Keeps clob s t)
    (a b c d : Word) : Op base o s { t with mem := st4 t.mem base o a b c d } := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem]
  exact st4_outside _ _ (by have := ho.2; omega) _ _ _ _

theorem fieldInit_ok (s : State) (v : BitVec 16 := 38) :
    WP isa (.block [.movz .w .x10 0 0, .movz .w .x11 v 0]) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x11 = v.setWidth 64 ∧ Keeps [.x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]
    rfl
  · rw [RegUpd.gpr_write_self, BitVec.shiftLeft_zero, BitVec.setWidth_setWidth (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

theorem zero4_ok (s : State) :
    WP isa (.block zero4) s fun t =>
      t.gpr .x4 = 0 ∧ t.gpr .x5 = 0 ∧ t.gpr .x6 = 0 ∧ t.gpr .x7 = 0 ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [zero4, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    RegUpd.gpr_write, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
