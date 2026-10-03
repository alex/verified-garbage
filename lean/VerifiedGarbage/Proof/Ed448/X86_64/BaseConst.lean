import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import VerifiedGarbage.Proof.X448.X86_64.Setup

/-!
# Ed448 base-point multiplication on x86-64: the constants

`consts`: the neutral point into slots 0–2, the base point into slots 8–10
and `d` into slot 11, each as its seven words stored by `stores`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keeps rv wv stores_E Outside)
open VG.Proof.X448 (toFe)
open VG.Impl.X448.X86_64 (W slot)

theorem loadWords_ok (s : State) (v : Nat) :
    WP isa (.block ((W.zip (words7 v)).map fun (r, x) => Instr.movImm64 r x)) s fun t =>
      rv t W = wv (words7 v) ∧ Keeps W s t := by
  apply WP.of_runBlock
  simp only [W, words7, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rv, wv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-- `constSlot i v`: slot `i` is `v`, if its seven words are `v`. -/
theorem constSlot_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) (v : Spec.X448.Fe)
    (hv : toFe (wv (words7 v.val)) = v) :
    WP isa (.block (constSlot i.val v)) s fun t =>
      E t.mem base = Function.update (E s.mem base) i v ∧ Outside base (slot i.val) 56 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [constSlot, WP.block_append_iff]
  refine WP.mono (loadWords_ok s v.val) fun a ⟨va, ka⟩ => ?_
  refine WP.mono (stores_E (hs.of_keeps ka (by decide)) i W rfl) fun t ⟨et, ot, gt, rdt, wrt⟩ =>
    ⟨by rw [et, va, hv, ka.2.1], by rw [← ka.2.1]; exact ot, fun r hr => (gt r).trans (ka.1 r hr),
      rdt.trans ka.2.2.1, wrt.trans ka.2.2.2⟩

theorem c0 : toFe (wv (words7 (0 : Spec.X448.Fe).val)) = 0 := by decide +kernel
theorem c1 : toFe (wv (words7 (1 : Spec.X448.Fe).val)) = 1 := by decide +kernel
theorem cBx : toFe (wv (words7 Spec.Ed448.basePoint.X.val)) = Spec.Ed448.basePoint.X := by
  decide +kernel
theorem cBy : toFe (wv (words7 Spec.Ed448.basePoint.Y.val)) = Spec.Ed448.basePoint.Y := by
  decide +kernel
theorem cd : toFe (wv (words7 Spec.Ed448.d.val)) = Spec.Ed448.d := by decide +kernel

theorem consts_eq : consts = constSlot (0 : Index).val 0 ++ (constSlot (1 : Index).val 1 ++
    (constSlot (2 : Index).val 1 ++ (constSlot (8 : Index).val Spec.Ed448.basePoint.X ++
    (constSlot (9 : Index).val Spec.Ed448.basePoint.Y ++ (constSlot (10 : Index).val 1 ++
    constSlot (11 : Index).val Spec.Ed448.d))))) := by
  simp only [consts, List.append_assoc]; rfl

/-- `consts`: `R` the neutral point, `Q` the base point, slot 11 `d`. -/
theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block consts) s fun t =>
      Proof.Ed448.X86_64.pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧
      Proof.Ed448.X86_64.pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Outside base 64 1584 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [consts_eq]
  have step : ∀ {x : State} (i : Index) (v : Spec.X448.Fe), toFe (wv (words7 v.val)) = v →
      Scr x base → ∀ {rest : List Instr} {Q : State → Prop},
      (∀ y, E y.mem base = Function.update (E x.mem base) i v → Outside base 64 1584 x.mem y.mem →
        (∀ r, r ∉ W → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr → Scr y base →
        WP isa (.block rest) y Q) →
      WP isa (.block (constSlot i.val v ++ rest)) x Q := by
    intro x i v hv hx rest Q k
    rw [WP.block_append_iff]
    refine WP.mono (constSlot_ok hx i v hv) fun y ⟨ey, oy, gy, rdy, wry⟩ =>
      k y ey (oy.mono (by simp only [slot]; omega) (by have := i.isLt; simp only [slot]; omega))
        gy rdy wry ⟨(gy _ (by decide)).trans hx.rdi, wry ▸ hx.wr, hx.nowrap⟩
  refine step 0 0 c0 hs fun s1 e1 o1 g1 rd1 wr1 hs1 => ?_
  refine step 1 1 c1 hs1 fun s2 e2 o2 g2 rd2 wr2 hs2 => ?_
  refine step 2 1 c1 hs2 fun s3 e3 o3 g3 rd3 wr3 hs3 => ?_
  refine step 8 _ cBx hs3 fun s4 e4 o4 g4 rd4 wr4 hs4 => ?_
  refine step 9 _ cBy hs4 fun s5 e5 o5 g5 rd5 wr5 hs5 => ?_
  refine step 10 1 c1 hs5 fun s6 e6 o6 g6 rd6 wr6 hs6 => ?_
  refine WP.mono (constSlot_ok hs6 11 _ cd) fun t ⟨et, ot, gt, rdt, wrt⟩ => ?_
  have O : Outside base 64 1584 s.mem t.mem :=
    o1.trans (o2.trans (o3.trans (o4.trans (o5.trans (o6.trans
      (ot.mono (by simp only [slot]; omega) (by simp only [slot]; omega)))))))
  refine ⟨?_, ?_, ?_, O, fun r hr => ?_, ?_, ?_⟩
  · rw [et, e6, e5, e4, e3, e2, e1]; rfl
  · rw [et, e6, e5, e4, e3, e2, e1]; rfl
  · simp only [et, Function.update_self]
  · rw [gt r hr, g6 r hr, g5 r hr, g4 r hr, g3 r hr, g2 r hr, g1 r hr]
  · rw [rdt, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wrt, wr6, wr5, wr4, wr3, wr2, wr1]

end VG.Proof.Ed448.X86_64
