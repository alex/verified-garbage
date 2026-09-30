import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.Carry

/-! Untrusted: memory and register frames for field operations. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

def clob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x20, .x21, .x22, .x23, .x24]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.fe {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : FieldRange d) : fe t.mem base d = fe s.mem base d :=
  h.mem.fe hd (by have := hd'.2; omega)

theorem Op.of_store {base : Addr} {o : Nat} {s t : State} (ho : FieldRange o) (h : Keeps clob s t)
    (a b c d : Word) : Op base o s { t with mem := st4 t.mem base o a b c d } := by
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
