import VerifiedGarbage.Proof.MlKem.X86_64.VArith
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.MlKem.X86_64.Vec

/-!
# ML-KEM on x86-64: coefficients in the words of SSE registers

Untrusted: everything here is checked by Lean. A register holds eight
coefficients (`Lanes`), and the butterflies `vbfly` and `vibfly` compute
eight butterflies of the specification at once (`vbfly_ok`, `vibfly_ok`),
from `q` and `q⁻¹` in `xmm15` and `xmm14` (`VConsts`), which `vconsts`
leaves there (`vconsts_ok`).

Blocks of SSE instructions only are run with `vrun`, which keeps the state a
chain of `setXmm`, whose registers the words' lemmas (`word_paddw`, …) read
lane by lane.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open W (qW qinvW)

/-- The words of `x` are the values of the coefficients `f 0, …, f 7`. -/
def Lanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ i < 8, (word x i).toNat = (f i).val

/-- The words of `x` are the zetas `ζ i · 2¹⁶ mod q` (Montgomery form). -/
def ZLanes (x : BitVec 128) (ζ : Nat → Zq) : Prop :=
  ∀ i < 8, (word x i).toNat = (ζ i).val * 65536 % 3329

/-- `q` in every word. -/
def qV : BitVec 128 := 0x0D010D010D010D010D010D010D010D01#128

/-- `q⁻¹ mod 2¹⁶` in every word. -/
def qinvV : BitVec 128 := 0xF301F301F301F301F301F301F301F301#128

theorem word_qV {i : Nat} (hi : i < 8) : word qV i = qW := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem word_qinvV {i : Nat} (hi : i < 8) : word qinvV i = qinvW := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The constants of the vector code are in place. -/
structure VConsts (s : State) : Prop where
  q : s.xmm .xmm15 = qV
  qinv : s.xmm .xmm14 = qinvV

/-- Everything but the SSE registers is as it was. -/
structure XKeep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem XKeep.refl (s : State) : XKeep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem XKeep.trans {s₁ s₂ s₃ : State} (h₁ : XKeep s₁ s₂) (h₂ : XKeep s₂ s₃) : XKeep s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.mxcsr.trans h₁.mxcsr⟩

theorem xmm_setXmm (s : State) (d : XReg) (v : BitVec 128) (r : XReg) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl
theorem mxcsr_setXmm (s : State) (d : XReg) (v : BitVec 128) : (s.setXmm d v).mxcsr = s.mxcsr := rfl

/-- Runs a block of SSE instructions. -/
syntax "vrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrun) => `(tactic| vrun [])
  | `(tactic| vrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
        Option.some.injEq, exists_eq_left', RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
        RegUpd.wr_setXmm, mxcsr_setXmm, xmm_setXmm, ite_true, ite_false, reduceCtorEq, $ls,*]))

/-! ## Montgomery products and conditional additions, word by word -/

/-- The words of `x` are `f 0, …, f 7`. -/
def WLanes (x : BitVec 128) (f : Nat → BitVec 16) : Prop := ∀ i < 8, word x i = f i

/-- Only the SSE registers `rs` changed. -/
structure XOnly (rs : List XReg) (s s' : State) : Prop extends XKeep s s' where
  xmm : ∀ r ∉ rs, s'.xmm r = s.xmm r

theorem XOnly.trans {rs rs' : List XReg} {s₁ s₂ s₃ : State} (h₁ : XOnly rs s₁ s₂) (h₂ : XOnly rs' s₂ s₃) :
    XOnly (rs ++ rs') s₁ s₃ :=
  { toXKeep := h₁.toXKeep.trans h₂.toXKeep
    xmm := fun r hr => by
      rw [List.mem_append, not_or] at hr
      rw [h₂.xmm r hr.2, h₁.xmm r hr.1] }

theorem XOnly.mono {rs rs' : List XReg} {s s' : State} (h : XOnly rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    XOnly rs' s s' := { toXKeep := h.toXKeep, xmm := fun r hr => h.xmm r fun h' => hr (hs r h') }

theorem XOnly.refl (rs : List XReg) (s : State) : XOnly rs s s :=
  { toXKeep := XKeep.refl s, xmm := fun _ _ => rfl }

theorem XOnly.setXmm {rs : List XReg} {s s' : State} {d : XReg} (hd : d ∈ rs) (h : XOnly rs s s')
    (v : BitVec 128) : XOnly rs s (s'.setXmm d v) :=
  { gpr := h.gpr, mem := h.mem, rd := h.rd, wr := h.wr, mxcsr := h.mxcsr
    xmm := fun r hr => by
      rw [xmm_setXmm, ifn (fun (e : r = d) => hr (e ▸ hd))]; exact h.xmm r hr }

/-- `XOnly` of a chain of `setXmm` of the registers `rs`. -/
syntax "xonly" : tactic
macro_rules
  | `(tactic| xonly) => `(tactic| (repeat (refine XOnly.setXmm (by simp) ?_ _)) <;> exact XOnly.refl _ _)

theorem VConsts.setXmm {s : State} (hc : VConsts s) {d : XReg} (h14 : XReg.xmm14 ≠ d)
    (h15 : XReg.xmm15 ≠ d) (v : BitVec 128) : VConsts (s.setXmm d v) :=
  ⟨by rw [xmm_setXmm, ifn h15]; exact hc.q, by rw [xmm_setXmm, ifn h14]; exact hc.qinv⟩

theorem XOnly.consts {rs : List XReg} {s s' : State} (h : XOnly rs s s') (hc : VConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VConsts s' :=
  ⟨by rw [h.xmm _ h15, hc.q], by rw [h.xmm _ h14, hc.qinv]⟩

theorem vmont_ok {d z t : XReg} (h2 : t ≠ d) (h3 : z ≠ t) (h5 : XReg.xmm15 ≠ d) (h6 : XReg.xmm14 ≠ t)
    (h7 : XReg.xmm15 ≠ t) {s : State} (hc : VConsts s) :
    WP isa (.block (vmont d z t)) s fun s' =>
      WLanes (s'.xmm d) (fun i => W.montW (word (s.xmm d) i) (word (s.xmm z) i)) ∧ XOnly [d, t] s s' := by
  simp only [vmont, xmov, xb]
  vrun [h2, h3, h5, h6, h7, h2.symm, h3.symm, h5.symm, h6.symm, h7.symm]
  refine ⟨fun i hi => ?_, ?_⟩
  swap
  · xonly
  rw [hc.q, hc.qinv]
  simp only [word_psubw _ _ hi, word_pmulhw _ _ hi, word_pmullw _ _ hi, word_movdqa, word_qV hi,
    word_qinvV hi]
  rfl

theorem vcadd_ok {d t : XReg} (h1 : t ≠ d) (h5 : XReg.xmm15 ≠ t) {s : State} (hc : VConsts s) :
    WP isa (.block (vcadd d t)) s fun s' =>
      WLanes (s'.xmm d) (fun i => W.caddW (word (s.xmm d) i)) ∧ XOnly [d, t] s s' := by
  simp only [vcadd, xmov, xb]
  vrun [h1, h5, h1.symm, h5.symm]
  refine ⟨fun i hi => ?_, ?_⟩
  swap
  · xonly
  rw [hc.q]
  simp only [word_paddw _ _ hi, word_pand _ _, word_psraw _ _ hi, word_movdqa, word_qV hi]
  rfl

theorem vcsub_ok {d t : XReg} (h1 : t ≠ d) (h4 : XReg.xmm15 ≠ d) (h5 : XReg.xmm15 ≠ t)
    (h6 : XReg.xmm14 ≠ d) {s : State} (hc : VConsts s) :
    WP isa (.block (vcsub d t)) s fun s' =>
      WLanes (s'.xmm d) (fun i => W.csubW (word (s.xmm d) i)) ∧ XOnly [d, t] s s' := by
  rw [vcsub, show (xb .psubw d .xmm15 :: vcadd d t) = [xb .psubw d .xmm15] ++ vcadd d t from rfl,
    WP.block_append_iff]
  simp only [xb]
  vrun [h4, h4.symm]
  refine WP.mono (vcadd_ok h1 h5 ⟨by rw [xmm_setXmm, ifn h4]; exact hc.q,
    by rw [xmm_setXmm, ifn h6]; exact hc.qinv⟩) fun s' ⟨hl, ho⟩ => ⟨fun i hi => ?_, ?_⟩
  · rw [hl i hi, xmm_setXmm, ifp rfl]; dsimp only; rw [word_psubw _ _ hi, hc.q, word_qV hi]; rfl
  · exact (XOnly.setXmm (by simp) (XOnly.refl [d] s) _ |>.trans ho).mono (by simp)

/-! ## Butterflies -/

theorem vbfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : Lanes (s.xmm .xmm0) x)
    (hy : Lanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) :
    WP isa (.block vbfly) s fun s' => Lanes (s'.xmm .xmm0) (fun i => x i + ζ i * y i) ∧
      Lanes (s'.xmm .xmm3) (fun i => x i - ζ i * y i) ∧ XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' := by
  rw [vbfly, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm1) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc) fun s1 ⟨l1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vcadd_ok (d := .xmm1) (t := .xmm2) (by decide) (by decide)
    (o1.consts hc (by decide) (by decide))) fun s2 ⟨l2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [show (xmov .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) ++
      (xb .psubw .xmm3 .xmm1 :: vcadd .xmm3 .xmm2) =
      [xmov .xmm3 .xmm0, xb .paddw .xmm0 .xmm1] ++ (vcsub .xmm0 .xmm2 ++
        ([xb .psubw .xmm3 .xmm1] ++ vcadd .xmm3 .xmm2)) from rfl, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  have c2 := o12.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vcsub_ok (d := .xmm0) (t := .xmm2) (by decide) (by decide) (by decide) (by decide)
    ((c2.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm0) (by decide) (by decide) _))
    fun s3 ⟨l3, o3⟩ => ?_
  rw [WP.block_append_iff]
  vrun
  have c3 := o3.consts ((c2.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm0) (by decide)
    (by decide) _) (by decide) (by decide)
  refine WP.mono (vcadd_ok (d := .xmm3) (t := .xmm2) (by decide) (by decide)
    (c3.setXmm (d := .xmm3) (by decide) (by decide) _)) fun s4 ⟨l4, o4⟩ => ?_
  -- the words of the registers along the way
  have w0 : s2.xmm .xmm0 = s.xmm .xmm0 := o12.xmm _ (by decide)
  have w13 : s1.xmm .xmm13 = s.xmm .xmm13 := o1.xmm _ (by decide)
  have w31 : s3.xmm .xmm1 = s2.xmm .xmm1 := by rw [o3.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  have w33 : s3.xmm .xmm3 = s2.xmm .xmm0 := by rw [o3.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  have w40 : s4.xmm .xmm0 = s3.xmm .xmm0 := by rw [o4.xmm _ (by decide), xmm_setXmm]; rfl
  have t : ∀ i < 8, word (s2.xmm .xmm1) i = W.caddW (W.montW (word (s.xmm .xmm1) i) (word (s.xmm .xmm13) i)) :=
    fun i hi => by rw [l2 i hi]; dsimp only; rw [l1 i hi]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [w40, l3 i hi, xmm_setXmm]; dsimp only
    rw [ifp rfl, word_paddw _ _ hi, t i hi, w0]
    exact (W.bflyW (hx i hi) (hy i hi) (hz i hi)).1
  · rw [l4 i hi, xmm_setXmm, ifp rfl]; dsimp only
    rw [word_psubw _ _ hi, w31, w33, t i hi, w0]
    exact (W.bflyW (hx i hi) (hy i hi) (hz i hi)).2
  · refine ((o12.trans ((XOnly.setXmm (by simp) (XOnly.setXmm (by simp) (XOnly.refl [.xmm3, .xmm0] s2) _) _).trans
      (o3.trans ((XOnly.setXmm (by simp) (XOnly.refl [.xmm3] s3) _).trans o4)))).mono ?_)
    simp

theorem vibfly_ok {s : State} (hc : VConsts s) {x y ζ : Nat → Zq} (hx : Lanes (s.xmm .xmm0) x)
    (hy : Lanes (s.xmm .xmm1) y) (hz : ZLanes (s.xmm .xmm13) ζ) :
    WP isa (.block vibfly) s fun s' => Lanes (s'.xmm .xmm0) (fun i => x i + y i) ∧
      Lanes (s'.xmm .xmm3) (fun i => ζ i * (y i - x i)) ∧ XOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' := by
  rw [vibfly, show (xmov .xmm3 .xmm1 :: xb .psubw .xmm3 .xmm0 :: xb .paddw .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) =
      [xmov .xmm3 .xmm1, xb .psubw .xmm3 .xmm0, xb .paddw .xmm0 .xmm1] ++ vcsub .xmm0 .xmm2 from rfl,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  simp only [xmov, xb]
  vrun
  rw [WP.block_append_iff]
  refine WP.mono (vcsub_ok (d := .xmm0) (t := .xmm2) (by decide) (by decide) (by decide) (by decide)
    (((hc.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm3) (by decide) (by decide)
      _).setXmm (d := .xmm0) (by decide) (by decide) _)) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts (((hc.setXmm (d := .xmm3) (by decide) (by decide) _).setXmm (d := .xmm3) (by decide)
    (by decide) _).setXmm (d := .xmm0) (by decide) (by decide) _) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (vmont_ok (d := .xmm3) (z := .xmm13) (t := .xmm2) (by decide) (by decide) (by decide)
    (by decide) (by decide) c1) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (vcadd_ok (d := .xmm3) (t := .xmm2) (by decide) (by decide)
    (o2.consts c1 (by decide) (by decide))) fun s3 ⟨l3, o3⟩ => ?_
  have w0 : s3.xmm .xmm0 = s1.xmm .xmm0 := (o2.trans o3).xmm _ (by decide)
  have w3 : s1.xmm .xmm3 = XBinOp.eval .psubw (s.xmm .xmm1) (s.xmm .xmm0) := by
    rw [o1.xmm _ (by decide), xmm_setXmm, xmm_setXmm, xmm_setXmm]; rfl
  have w13 : s1.xmm .xmm13 = s.xmm .xmm13 := by rw [o1.xmm _ (by decide), xmm_setXmm, xmm_setXmm, xmm_setXmm]; rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [w0, l1 i hi, xmm_setXmm]; dsimp only
    rw [ifp rfl, word_paddw _ _ hi]
    exact (W.ibflyW (hx i hi) (hy i hi) (hz i hi)).1
  · rw [l3 i hi]; dsimp only; rw [l2 i hi]; dsimp only; rw [w3, w13, word_psubw _ _ hi]
    exact (W.ibflyW (hx i hi) (hy i hi) (hz i hi)).2
  · refine ((((XOnly.setXmm (by simp) (XOnly.setXmm (by simp) (XOnly.setXmm (by simp)
      (XOnly.refl [.xmm3, .xmm0] s) _) _) _).trans o1).trans (o2.trans o3)).mono ?_)
    simp

end VG.Proof.MlKem.X86_64
