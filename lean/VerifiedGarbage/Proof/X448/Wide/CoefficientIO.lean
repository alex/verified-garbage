import VerifiedGarbage.Proof.X448.Wide.AddCoefficient

/-! Untrusted: coefficient reads and writes inside the X448 scratch buffer. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64

theorem loadAt_ok {s : State} {base : Addr} (hs : Scr s base) {o k : Nat}
    (ho : o + 16 * k + 16 ≤ 8192) (ho8 : o % 8 = 0) :
    WP isa (.block [ld .x4 (o + 16 * k), ld .x5 (o + 16 * k + 8)]) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = coeff s.mem base o k ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have ae : (o + 16 * k) % 8 = 0 ∧ o + 16 * k < 32768 := ⟨by omega, by omega⟩
  have be : (o + 16 * k + 8) % 8 = 0 ∧ o + 16 * k + 8 < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := o + 16 * k) (n := 8) (by omega)
  have bl := hs.read (d := o + 16 * k + 8) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeAt_ok {s : State} {base : Addr} (hs : Scr s base) {o k : Nat}
    (ho : o + 16 * k + 16 ≤ 8192) (ho8 : o % 8 = 0)
    (r0 : Reg := .x4) (r1 : Reg := .x5) :
    WP isa (.block [st r0 (o + 16 * k), st r1 (o + 16 * k + 8)]) s fun t =>
      t.mem = putCoeff s.mem base o k (s.gpr r0) (s.gpr r1) ∧ Keeps [] s t := by
  have ae : (o + 16 * k) % 8 = 0 ∧ o + 16 * k < 32768 := ⟨by omega, by omega⟩
  have be : (o + 16 * k + 8) % 8 = 0 ∧ o + 16 * k + 8 < 32768 := ⟨by omega, by omega⟩
  have aw := hs.write (d := o + 16 * k) (n := 8) (by omega)
  have bw := hs.write (d := o + 16 * k + 8) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

end VG.Proof.X448.Wide
