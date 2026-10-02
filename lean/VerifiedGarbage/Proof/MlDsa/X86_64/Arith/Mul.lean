import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

Untrusted: everything here is checked by Lean. A doubleword of `mulV x y`
is the product of those of `x` and `y` (`mul_lane`): `mont` of `mont` of
their product by `2⁶⁴ mod q` (`mont_mont_R2`). The loop stores four of them
at a time to the first 252 coefficients of `h` (`Mul.step`, `Mul.loop_ok`),
inside `withMxcsr` through the last 8 bytes of `h`; the last four are
computed from the coefficients of `h` loaded before (`Mul.last`), and stored
after MXCSR is loaded back (`Mul.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly WP.keep writesOnly gprPreserved_of ifn xmm_setXmm wp_rcxLoop
  add_ofNat_zero)
open VG.Impl.MlKem.X86_64 (xb xmov rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced)

/-! ## Four products -/

/-- `2⁶⁴ mod q` in each doubleword, as the prologue leaves it in `xmm11`. -/
def r2V : BitVec 128 := shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 2365951#32) 0

theorem dword_r2V {i : Nat} (hi : i < 4) : dword r2V i = 2365951#32 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide

/-- What `mulCore` leaves in `xmm3` of the vectors of `f` and `g`. -/
def mulV (x y : BitVec 128) : BitVec 128 := csubV (montV (montV x y (shufDwords y 0xF5)) r2V r2V)

/-- What `mulAddCore` leaves in `xmm3`, with the vector of `h`. -/
def mulAddV (x y z : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddd (mulV x y) z)

theorem mul_lane {x y : BitVec 128} {a b : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b) {i : Nat}
    (hi : i < 4) : (dword (mulV x y) i).toNat = (a i * b i).val := by
  have hzo : ZOdd y (shufDwords y 0xF5) := fun j hj => by
    rw [dword_shufDwords _ _ (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have hb1 : ∀ i < 4, (dword x i).toNat * (dword y i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [hx i hi, hy i hi]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (val_lt (a i)) (Nat.le_of_lt (val_lt (b i)))
      (by decide)) (by decide)
  have m1 := fun i (hi : i < 4) => dword_montV hzo hb1 hi
  have hb2 : ∀ i < 4, (dword (montV x y (shufDwords y 0xF5)) i).toNat * (dword r2V i).toNat < q * 2 ^ 32 :=
    fun i hi => by
      rw [m1 i hi, dword_r2V hi]
      have := mont_lt (hb1 i hi)
      rw [q_eq] at this ⊢
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le this (Nat.le_refl 2365951) (by decide)) (by decide)
  have hzo2 : ZOdd r2V r2V := fun j hj => by rw [dword_r2V (by omega), dword_r2V (by omega)]
  rw [mulV, dword_csubV _ hi, csubL_toNat (by rw [dword_montV hzo2 hb2 hi]; exact mont_lt (hb2 i hi)),
    dword_montV hzo2 hb2 hi, condSub_mont (hb2 i hi), m1 i hi, dword_r2V hi,
    show (2365951#32).toNat = 2 ^ 64 % q from rfl, mont_mont_R2, hx i hi, hy i hi, val_mul]

theorem mulAdd_lane {x y z : BitVec 128} {a b c : Nat → Zq} (hx : DLanes x a) (hy : DLanes y b)
    (hz : DLanes z c) {i : Nat} (hi : i < 4) : (dword (mulAddV x y z) i).toNat = (c i + a i * b i).val := by
  have hm := mul_lane hx hy hi
  rw [mulAddV, dword_csubV _ hi, dword_paddd _ _ hi, addD_toNat (by rw [hm]; exact val_lt _)
    (by rw [hz i hi]; exact val_lt _), hm, hz i hi, Nat.add_comm, ← val_add]

theorem mulCore_ok {s : State} (hc : VConsts s) (h11 : s.xmm .xmm11 = r2V) :
    WP isa (.block mulCore) s fun s' =>
      s'.xmm .xmm3 = mulV (s.xmm .xmm3) (s.xmm .xmm13) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [mulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, h11]
  exact ⟨rfl, by xonly⟩

theorem mulAddCore_ok {s : State} (hc : VConsts s) (h11 : s.xmm .xmm11 = r2V) :
    WP isa (.block mulAddCore) s fun s' =>
      s'.xmm .xmm3 = mulAddV (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧
        XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s' := by
  simp only [mulAddCore, mulCore, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, h11]
  exact ⟨rfl, by xonly⟩

theorem mulPro_ok (s : State) :
    WP isa (.block mulPro) s fun s' => VConsts s' ∧ s'.xmm .xmm11 = r2V ∧ s'.xmm .xmm6 = s.xmm .xmm6 ∧
      Keep [.rax] s s' ∧ s'.mem = s.mem := by
  simp only [mulPro, vconsts, List.cons_append, List.nil_append]
  vrund
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]

/-! ## The loop -/

namespace Mul

theorem ptr16 (p : Addr) (i : Nat) : coeffAddr p (4 * i) + 16 = p + BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [coeffAddr, BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2; omega

/-- After `i` iterations: the first `4i` coefficients of `h` are `R`'s, the
others as they were in `s₀`. -/
structure Inv (h f g : Addr) (s₀ : State) (R : Poly) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = h + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = f + BitVec.ofNat 64 (16 * i)
  rdx : s.gpr .rdx = g + BitVec.ofNat 64 (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : VConsts s
  r2 : s.xmm .xmm11 = r2V
  x6 : s.xmm .xmm6 = s₀.xmm .xmm6
  frame : Frame [pR h] s₀.mem s.mem
  done : ∀ k < 4 * i, (coeffAt s.mem h k).toNat = (R[k]!).val
  rest : ∀ k < 256, 4 * i ≤ k → coeffAt s.mem h k = coeffAt s₀.mem h k

section
variable {h f g : Addr} {s₀ : State} (hwh : pR h ∈ s₀.wr) (hrf : pR f ∈ s₀.rd ++ s₀.wr)
  (hrg : pR g ∈ s₀.rd ++ s₀.wr) (hdf : (pR h).Disjoint (pR f)) (hdg : (pR h).Disjoint (pR g))
  {F G : Poly} (hF : ∀ k < 256, (coeffAt s₀.mem f k).toNat = (F[k]!).val)
  (hG : ∀ k < 256, (coeffAt s₀.mem g k).toNat = (G[k]!).val)
  {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
  (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
    s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
  {R : Poly} {H : Nat → BitVec 32} (hH : ∀ k < 252, coeffAt s₀.mem h k = H k)
  (hlane : ∀ i < 64, ∀ x y z : BitVec 128, (∀ e < 4, (dword x e).toNat = (F[4 * i + e]!).val) →
    (∀ e < 4, (dword y e).toNat = (G[4 * i + e]!).val) → (∀ e < 4, dword z e = H (4 * i + e)) →
    ∀ e < 4, (dword (Fv x y z) e).toNat = (R[4 * i + e]!).val)
include hwh hrf hrg hdf hdg hF hG hcore hH hlane

theorem step {i : Nat} (hi : i < 63) {s : State} (hI : Inv h f g s₀ R i s) :
    WP isa (.block (mulLoads ++ core ++ mulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv h f g s₀ R (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have e1 : s.gpr .rdi = coeffAddr h (4 * i) := by rw [hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi = coeffAddr f (4 * i) := by rw [hI.rsi]; congr 2; omega
  have e3 : s.gpr .rdx = coeffAddr g (4 * i) := by rw [hI.rdx]; congr 2; omega
  have rf : InRegions (s.rd ++ s.wr) (coeffAddr f (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains f j0⟩
  have rg : InRegions (s.rd ++ s.wr) (coeffAddr g (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains g j0⟩
  have rh : InRegions (s.rd ++ s.wr) (coeffAddr h (4 * i)) 16 := by
    rw [hI.rd, hI.wr]; exact f_in (List.mem_append_right _ hwh) j0
  have wh : InRegions s.wr (coeffAddr h (4 * i)) 16 := by rw [hI.wr]; exact f_in hwh j0
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [show mulLoads ++ core ++ mulTail ++ [.alu .sub .rcx (.imm 1)] =
    mulLoads ++ (core ++ (mulTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) by simp [List.append_assoc],
    WP.block_append_iff]
  simp only [mulLoads]
  vrund [e1, e2, e3, rf, rg, rh]
  rw [WP.block_append_iff]
  refine WP.mono (hcore _ (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2))
    fun s2 ⟨h3, o2⟩ => ?_
  have c2 := xonly_vconsts o2 (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by decide) (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have r2 : s2.rd = s.rd := o2.rd
  have w2 : s2.wr = s.wr := o2.wr
  have x11 : s2.xmm .xmm11 = r2V := by rw [o2.xmm _ (by decide)]; simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2
  simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false] at h3
  generalize hV : Fv (s.mem.readW (coeffAddr f (4 * i)) 128) (s.mem.readW (coeffAddr g (4 * i)) 128)
    (s.mem.readW (coeffAddr h (4 * i)) 128) = V at h3
  simp only [mulTail]
  vrund [g2, m2, r2, w2, e1, e2, e3, wh, h3]
  have lx : ∀ e < 4, (dword (s.mem.readW (coeffAddr f (4 * i)) 128) e).toNat = (F[4 * i + e]!).val :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega)]
  have ly : ∀ e < 4, (dword (s.mem.readW (coeffAddr g (4 * i)) 128) e).toNat = (G[4 * i + e]!).val :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega)]
  have lz : ∀ e < 4, dword (s.mem.readW (coeffAddr h (4 * i)) 128) e = H (4 * i + e) :=
    fun e he => by rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, hI.rest _ (by omega) (by omega),
      hH _ (by omega)]
  have hl := hlane i (by omega) _ _ _ lx ly lz
  rw [hV] at hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
      RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.xmm_setReg,
      RegUpd.xmm_setFlags, ite_true, ite_false, reduceCtorEq]
  · exact ptr16 h i
  · exact ptr16 f i
  · exact ptr16 g i
  · exact hI.rd
  · exact hI.wr
  · exact c2.q
  · exact c2.qinv
  · exact x11
  · rw [o2.xmm _ (by decide)]; simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.x6
  · exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains h j0)
  · intro k hk
    rw [coeffAt_write128 _ _ j0 _ (by omega)]
    split
    · rw [hl _ (by omega), show 4 * i + (k - 4 * i) = k by omega]
    · exact hI.done k (by omega)
  · intro k hk hk'
    rw [coeffAt_write128 _ _ j0 _ hk, ifn (by omega)]
    exact hI.rest k hk (by omega)

theorem loop_ok (hdi : s₀.gpr .rdi = h) (hsi : s₀.gpr .rsi = f) (hdx : s₀.gpr .rdx = g) (hc : VConsts s₀)
    (h11 : s₀.xmm .xmm11 = r2V) : WP isa (rcxLoop 63 (mulLoads ++ core ++ mulTail)) s₀ (Inv h f g s₀ R 63) :=
  wp_rcxLoop (N := 63) (by decide) (by decide) _ (fun u o _ =>
    ⟨by rw [o.keep.gpr (by decide), hdi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hsi, Nat.mul_zero, add_ofNat_zero],
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, add_ofNat_zero], o.keep.2.1, o.keep.2.2,
      ⟨by rw [o.xmm]; exact hc.q, by rw [o.xmm]; exact hc.qinv⟩, by rw [o.xmm]; exact h11, by rw [o.xmm],
      by rw [o.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega), fun k _ _ => by rw [o.mem]⟩)
    fun i hi u hI => step hwh hrf hrg hdf hdg hF hG hcore hH hlane hi hI


omit hwh hH in
/-- The last four coefficients, with those of `h` in `xmm6`. -/
theorem last {s : State} (hI : Inv h f g s₀ R 63 s) (hz : ∀ e < 4, dword (s₀.xmm .xmm6) e = H (252 + e)) :
    WP isa (.block (mulLast core)) s fun s' =>
      (∀ e < 4, (dword (s'.xmm .xmm3) e).toNat = (R[252 + e]!).val) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem := by
  have j0 : 4 * 63 + 4 ≤ 256 := by decide
  have e2 : s.gpr .rsi = coeffAddr f (4 * 63) := hI.rsi
  have e3 : s.gpr .rdx = coeffAddr g (4 * 63) := hI.rdx
  have rf : InRegions (s.rd ++ s.wr) (coeffAddr f (4 * 63)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrf, pR_contains f j0⟩
  have rg : InRegions (s.rd ++ s.wr) (coeffAddr g (4 * 63)) 16 := by
    rw [hI.rd, hI.wr]; exact ⟨_, hrg, pR_contains g j0⟩
  have mf : ∀ k < 256, coeffAt s.mem f k = coeffAt s₀.mem f k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdf.symm) (by rw [n_eq]; exact hk)
  have mg : ∀ k < 256, coeffAt s.mem g k = coeffAt s₀.mem g k := fun k hk =>
    coeffAt_frame hI.frame (by simpa using hdg.symm) (by rw [n_eq]; exact hk)
  rw [mulLast, WP.block_append_iff]
  vrund [e2, e3, rf, rg, eval_movdqa]
  refine WP.mono (hcore _ (((hI.c.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _).setXmm
    (by decide) (by decide) _) (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hI.r2))
    fun s2 ⟨h3, o2⟩ => ⟨fun e he => ?_, o2.gpr, o2.mem⟩
  simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false, hI.x6] at h3
  rw [h3]
  refine hlane 63 (by decide) _ _ _ (fun e he => ?_) (fun e he => ?_) hz e he
  · rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mf _ (by omega), hF _ (by omega)]
  · rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, mg _ (by omega), hG _ (by omega)]

end


theorem coeffAt_mxH {m m' : Mem} {p : Addr} (hf : Frame [mxH p] m m') {k : Nat} (hk : k < 254) :
    coeffAt m' p k = coeffAt m p k :=
  hf.readW (r := ⟨coeffAddr p k, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint p (by omega) (by omega) (by omega)) (by decide)

/-- The whole function, from its precondition, with a `core` whose lanes are
those of `t`. -/
theorem fn_ok {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} {σ : State} (hp : (mulK t hPre).pre σ)
    {core : List Instr} {Fv : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hcore : ∀ s : State, VConsts s → s.xmm .xmm11 = r2V → WP isa (.block core) s fun s' =>
      s'.xmm .xmm3 = Fv (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm5) ∧ XOnly [.xmm12, .xmm3, .xmm2, .xmm4] s s')
    (hlane : ∀ i < 64, ∀ x y z : BitVec 128,
      (∀ e < 4, (dword x e).toNat = ((polyAt σ.mem (σ.gpr .rsi))[4 * i + e]!).val) →
      (∀ e < 4, (dword y e).toNat = ((polyAt σ.mem (σ.gpr .rdx))[4 * i + e]!).val) →
      (∀ e < 4, dword z e = coeffAt σ.mem (σ.gpr .rdi) (4 * i + e)) →
      ∀ e < 4, (dword (Fv x y z) e).toNat = ((t (polyAt σ.mem (σ.gpr .rdi)) (polyAt σ.mem (σ.gpr .rsi))
        (polyAt σ.mem (σ.gpr .rdx)))[4 * i + e]!).val)
    (hk : writesOnly [.rax, .rdi, .rsi, .rdx, .rcx]
      (.seq (.block mulPro) (.seq (rcxLoop 63 (mulLoads ++ core ++ mulTail)) (.block (mulLast core)))) = true) :
    WP isa (mulFn core) σ fun s' => Keep [.r8, .rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] σ s' ∧
      Frame [pR (σ.gpr .rdi)] σ.mem s'.mem ∧ (mulK t hPre).post σ s' := by
  obtain ⟨hrd, hwr, hdf, hdg, -, -, -, -, redf, redg⟩ := hp
  generalize eh : σ.gpr .rdi = h at *
  generalize ef : σ.gpr .rsi = f at *
  generalize eg : σ.gpr .rdx = g at *
  let R := t (polyAt σ.mem h) (polyAt σ.mem f) (polyAt σ.mem g)
  have hwh : pR h ∈ σ.wr := by rw [hwr]; exact List.mem_singleton_self _
  have r6 : InRegions (σ.rd ++ σ.wr) (coeffAddr h 252) 16 :=
    ⟨_, List.mem_append_right _ hwh, Offset.contains_base h (by omega) (by omega)⟩
  simp only [mulFn]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r8 = h ∧
      s1.xmm .xmm6 = σ.mem.readW (coeffAddr h 252) 128 ∧ Keep [.r8] σ s1 ∧ s1.mem = σ.mem) (by
    vrund [eh, r6]
    exact ⟨fun r hr => by
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg, hr, ite_false], rfl, rfl⟩) fun s1 ⟨h8, h6, k1, m1⟩ => ?_)
  have hw1 : pR h ∈ s1.wr := by rw [k1.2.2]; exact hwh
  refine WP.seq (WP.mono (withMxcsrH_ok (r := .r8) ⟨by decide, by decide⟩ [.rax, .rdi, .rsi, .rdx, .rcx]
    ⟨by decide, by decide⟩ h8 hw1 hk (Q := fun (s3 : State) => Keep [.rax, .r11, .rax, .rdi, .rsi, .rdx, .rcx] s1 s3 ∧
      s3.gpr .rdi = coeffAddr h 252 ∧ Frame [pR h] σ.mem s3.mem ∧
      (∀ k < 252, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
      ∀ e < 4, (dword (s3.xmm .xmm3) e).toNat = (R[252 + e]!).val)
    fun s2 k2 f2 x2 _ => ?_) fun s4 ⟨s3, ⟨kk, hdi, fr, dn, ln⟩, f4, k4, x4, _⟩ => ?_)
  · have fσ2 : Frame [mxH h] σ.mem s2.mem := by rw [← m1]; exact f2
    refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx] (WP.seq (WP.mono (mulPro_ok s2)
      fun w ⟨cw, xw, x6, kw, mw⟩ => ?_) (Q := fun (s3 : State) => s3.gpr .rdi = coeffAddr h 252 ∧
        Frame [pR h] σ.mem s3.mem ∧ (∀ k < 252, (coeffAt s3.mem h k).toNat = (R[k]!).val) ∧
        ∀ e < 4, (dword (s3.xmm .xmm3) e).toNat = (R[252 + e]!).val)) hk)
      fun s3 ⟨q3, kk⟩ => ⟨k2.trans kk, q3⟩
    have gw : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r8 → w.gpr r = σ.gpr r := fun r h1 h2 h3 => by
      rw [kw.gpr (by simpa using h1), k2.gpr (by simp [h1, h2]), k1.gpr (by simpa using h3)]
    have rw' : w.rd = σ.rd ∧ w.wr = σ.wr :=
      ⟨kw.2.1.trans (k2.2.1.trans k1.2.1), kw.2.2.trans (k2.2.2.trans k1.2.2)⟩
    have fσw : Frame [mxH h] σ.mem w.mem := by rw [mw]; exact fσ2
    have fσw' : Frame [pR h] σ.mem w.mem :=
      Frame.sub fσw fun r hr => ⟨pR h, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine WP.seq (WP.mono (loop_ok (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.2]; exact hwh) (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore (fun k hk => coeffAt_mxH fσw (by omega)) hlane
      (by rw [gw _ (by decide) (by decide) (by decide), eh]) (by rw [gw _ (by decide) (by decide) (by decide), ef])
      (by rw [gw _ (by decide) (by decide) (by decide), eg]) cw xw) fun s hI => ?_)
    refine WP.mono (last (s₀ := w) (h := h) (f := f) (g := g) (R := R) (F := polyAt σ.mem f)
      (G := polyAt σ.mem g) (H := coeffAt σ.mem h)
      (by rw [rw'.1, hrd]; simp) (by rw [rw'.1, hrd]; simp) hdf hdg
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdf.symm) (by rw [n_eq]; exact hk),
          polyAt_val redf (by rw [n_eq]; exact hk)])
      (fun k hk => by
        rw [coeffAt_frame fσw' (by simpa using hdg.symm) (by rw [n_eq]; exact hk),
          polyAt_val redg (by rw [n_eq]; exact hk)])
      hcore hlane hI (fun e he => by
        rw [x6, x2, h6, dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq])) fun s3 ⟨ln, g3, m3⟩ => ?_
    refine ⟨by rw [g3, hI.rdi], ?_, fun k hk => by rw [m3]; exact hI.done k (by omega), ln⟩
    rw [m3]
    exact Frame.trans fσw' hI.frame
  · have k14 := (k1.trans kk).trans k4
    have hdi4 : s4.gpr .rdi = coeffAddr h 252 := by rw [k4.gpr (by simp), hdi]
    have wh4 : InRegions s4.wr (coeffAddr h 252) 16 := by
      rw [k14.2.2]; exact ⟨_, hwh, Offset.contains_base h (by omega) (by omega)⟩
    vrund [hdi4, wh4]
    have f4' : Frame [pR h] s3.mem s4.mem := Frame.sub f4 fun r hr => ⟨pR h, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact mxH_sub h⟩
    refine ⟨k14.mono (by simp), (fr.trans f4').writeW (List.mem_singleton_self _) _
      (Offset.contains_base h (by omega) (by omega)), ?_⟩
    dsimp only [mulK]
    rw [eh, ef, eg]
    refine polyIs_of_toNat fun k hk => ?_
    rw [n_eq] at hk
    rw [coeffAt_write128 _ _ (j := 252) (by decide) _ hk]
    split
    · rw [x4]
      have := ln (k - 252) (by omega)
      rwa [show 252 + (k - 252) = k by omega] at this
    · rw [coeffAt_mxH f4 (by omega)]
      exact dn k (by omega)

end Mul

/-! ## The functions -/

/-- The contract of `vg_mldsa_multiply_ntt`. -/
abbrev mulK' : Contract isa := mulK (fun _ f g => Spec.MlDsa.multiplyNTT f g) fun _ _ => True

/-- The contract of `vg_mldsa_multiply_add_ntt`. -/
abbrev mulAddK : Contract isa := mulK (fun h f g => Spec.MlDsa.add h (Spec.MlDsa.multiplyNTT f g)) Reduced

theorem mul_correct (s : State) (hs : mulK'.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mul s t s' ∧ abiPreserved s s' ∧ mulK'.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := Mul.fn_ok hs (core := mulCore) (Fv := fun x y _ => mulV x y)
    (fun s hc h11 => mulCore_ok hc h11)
    (fun i hi x y z hx hy _ e he => by
      rw [mul_get _ _ (by rw [n_eq]; omega)]
      exact mul_lane hx hy he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

theorem mulAdd_correct (s : State) (hs : mulAddK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mulAdd s t s' ∧ abiPreserved s s' ∧ mulAddK.post s s' := by
  obtain ⟨t, s', he, hk, hf, hq⟩ := Mul.fn_ok hs (core := mulAddCore) (Fv := mulAddV)
    (fun s hc h11 => mulAddCore_ok hc h11)
    (fun i hi x y z hx hy hz e he => by
      rw [add_get _ _ (by rw [n_eq]; omega), mul_get _ _ (by rw [n_eq]; omega)]
      exact mulAdd_lane hx hy (c := fun e => (polyAt s.mem (s.gpr .rdi))[4 * i + e]!)
        (fun e he => by rw [hz e he, polyAt_val hs.2.2.2.2.2.2.2.1 (by rw [n_eq]; omega)]) he)
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hq⟩

/-- The pointers and `rsp` are public. -/
def mulτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]

theorem mul_agree {t : Poly → Poly → Poly → Poly} {r : Mem → Addr → Prop} (s₁ s₂ : State) (_ : (mulK t r).pre s₁)
    (_ : (mulK t r).pre s₂) (hp : (mulK t r).pub s₁ s₂) : X86_64.Taint.Agree mulτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

theorem mul_ct : ConstantTime isa mulK'.pre mulK'.pub Impl.MlDsa.X86_64.Arith.mul :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem mulAdd_ct : ConstantTime isa mulAddK.pre mulAddK.pub Impl.MlDsa.X86_64.Arith.mulAdd :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mul (Spec.MlDsa.mulContract X86_64.abi) :=
  Verified.of_correct mul_correct mul_ct (by
    mldsa_implies [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

theorem mulAdd_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mulAdd (Spec.MlDsa.mulAddContract X86_64.abi) :=
  Verified.of_correct mulAdd_correct mulAdd_ct (by
    mldsa_implies [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.X86_64.Arith
