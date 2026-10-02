import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub

/-!
# ML-DSA on AArch64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

The body stores the value `v i` to coefficient `i` of `h` (`mulBody_ok`,
`mulAddBody_ok`); the loop is proven once for any such body (`Mul.fn_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## The constants -/

/-- The constants of `reduce` are in their registers. -/
structure Consts (s : State) : Prop where
  x9 : s.gpr .x9 = Qv
  x10 : s.gpr .x10 = negQ
  x11 : s.gpr .x11 = Mv

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' => (Consts s' ∧ s'.mem = s.mem) ∧ Keep [.x9, .x10, .x11] s s' := by
  unfold consts
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x9 _ s) fun s₁ ⟨⟨h9, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movImm_ok .x10 _ s₁) fun s₂ ⟨⟨h10, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (movImm_ok .x11 _ s₂) fun s₃ ⟨⟨h11, hm₃⟩, k₃⟩ =>
    ⟨⟨⟨?_, by rw [k₃.get .x10, h10], h11⟩, by rw [hm₃, hm₂, hm₁]⟩, ((k₁.trans k₂).trans k₃).mono⟩
  rw [k₃.get .x9, k₂.get .x9, h9]; exact q32

/-! ## One coefficient -/

theorem mulBody_ok (s : State) (hc : Consts s) (h0 : InRegions s.wr (s.gpr .x0) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h2 : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4) :
    WP isa (.block mulBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0)
          ((redX (w64 (s.mem.readW (s.gpr .x1) 32) * w64 (s.mem.readW (s.gpr .x2) 32))).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x2, .x12, .x13, .x14] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold mulBody mulHead reduce Impl.MlKem.AArch64.csub step3
  arun [h0, h1, h2, hc.x9, hc.x10, hc.x11, redX, csubX]

theorem mulAddBody_ok (s : State) (hc : Consts s) (h0 : InRegions s.wr (s.gpr .x0) 4)
    (h0' : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h2 : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4) :
    WP isa (.block mulAddBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0)
          ((redX (w64 (s.mem.readW (s.gpr .x1) 32) * w64 (s.mem.readW (s.gpr .x2) 32) +
            w64 (s.mem.readW (s.gpr .x0) 32))).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x2, .x12, .x13, .x14] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold mulAddBody mulAddHead mulHead reduce Impl.MlKem.AArch64.csub step3
  arun [h0, h0', h1, h2, hc.x9, hc.x10, hc.x11, redX, csubX]

/-! ## The values -/

/-- A product of words of values `x` and `y`, reduced. -/
theorem redX_mulW {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((redX (w64 a * w64 b)).setWidth 32).toNat = (x * y).val := by
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.val * y.val < q * q := Nat.mul_lt_mul_of_lt_of_lt hx hy
  have e : (w64 a * w64 b).toNat = x.val * y.val := by
    rw [BitVec.toNat_mul, toNat_setWidth64, toNat_setWidth64, ha, hb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hxy (by decide))
  rw [redX32 (by rw [e]; exact hxy), e, val_mul]

/-- A product of words of values `x` and `y` plus one of value `z`, reduced. -/
theorem redX_mulAddW {a b c : BitVec 32} {x y z : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hc : c.toNat = z.val) : ((redX (w64 a * w64 b + w64 c)).setWidth 32).toNat = (z + x * y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hz : z.val < 8380417 := z.isLt
  have hxy : x.val * y.val ≤ 8380416 * 8380416 := Nat.mul_le_mul (by omega) (by omega)
  have hl : x.val * y.val + z.val < q * q := by
    rw [show q * q = 70231389093889 from rfl]; omega
  have e : (w64 a * w64 b + w64 c).toNat = x.val * y.val + z.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_setWidth64, toNat_setWidth64, toNat_setWidth64, ha, hb, hc,
      Nat.mod_eq_of_lt (a := x.val * y.val) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hl (by decide))
  rw [redX32 (by rw [e]; exact hl), e, val_add', val_mul, Nat.add_mod_mod, Nat.add_comm]

/-! ## The loop -/

namespace Mul

/-- After `i` coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = coeffAddr (s₀.gpr .x0) i
  x1 : s.gpr .x1 = coeffAddr (s₀.gpr .x1) i
  x2 : s.gpr .x2 = coeffAddr (s₀.gpr .x2) i
  consts : Consts s
  keep : Keep [.x0, .x1, .x2, .x9, .x10, .x11, .x12, .x13, .x14] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .x0) k = if k < i then v k else coeffAt s₀.mem (s₀.gpr .x0) k

/-- The body stores `v i` to coefficient `i`. -/
def BodyOk (s₀ : State) (body : List Instr) (v : Nat → BitVec 32) : Prop :=
  ∀ i < 256, ∀ s, Inv s₀ v i s → WP isa (.block body) s fun s' =>
    (s'.mem = s.mem.writeW (s.gpr .x0) (v i) ∧ s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧
      s'.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1) ∧
    Keep [.x0, .x1, .x2, .x12, .x13, .x14] s s'

section
variable {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} {s₀ : State}
  (hp : (mulK t hPre).pre s₀)
include hp

/-- The accesses of iteration `i`, and the words it reads. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s : State} (hI : Inv s₀ v i s) :
    s.mem.readW (s.gpr .x0) 32 = coeffAt s₀.mem (s₀.gpr .x0) i ∧
      s.mem.readW (s.gpr .x1) 32 = coeffAt s₀.mem (s₀.gpr .x1) i ∧
      s.mem.readW (s.gpr .x2) 32 = coeffAt s₀.mem (s₀.gpr .x2) i ∧
      InRegions s.wr (s.gpr .x0) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .x0) 4 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .x1) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .x2) 4 := by
  have hrd : s.rd = [pR (s₀.gpr .x1), pR (s₀.gpr .x2)] := hI.keep.rd.trans hp.1
  have hwr : s.wr = [pR (s₀.gpr .x0)] := hI.keep.wr.trans hp.2.1
  rw [hI.x0, hI.x1, hI.x2, hrd, hwr]
  refine ⟨?_, ?_, ?_, ⟨_, by simp, coeff_contains _ hi⟩, ⟨_, by simp, coeff_contains _ hi⟩,
    ⟨_, by simp, coeff_contains _ hi⟩, ⟨_, by simp, coeff_contains _ hi⟩⟩
  · rw [← coeffAt_eq, hI.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · rw [← coeffAt_eq]
    exact coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) hi
  · rw [← coeffAt_eq]
    exact coeffAt_frame hI.frame (by simpa using hp.2.2.2.1.symm) hi

end

theorem inv_step {s₀ : State} {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s s' : State}
    (hI : Inv s₀ v i s) (hm : s'.mem = s.mem.writeW (s.gpr .x0) (v i))
    (h0 : s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4) (h1 : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4)
    (h2 : s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4) (hk : Keep [.x0, .x1, .x2, .x12, .x13, .x14] s s') :
    Inv s₀ v (i + 1) s' where
  x0 := by rw [h0, hI.x0, coeffAddr_next]
  x1 := by rw [h1, hI.x1, coeffAddr_next]
  x2 := by rw [h2, hI.x2, coeffAddr_next]
  consts := ⟨by rw [hk.get .x9, hI.consts.x9], by rw [hk.get .x10, hI.consts.x10],
    by rw [hk.get .x11, hI.consts.x11]⟩
  keep := (hI.keep.trans hk).mono
  frame := by
    rw [hm, hI.x0]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)
  coeff k hk := by
    rw [hm, hI.x0, coeffAt_writeW _ _ hk hi, hI.coeff k hk]
    by_cases e : i = k
    · subst e; simp
    · have : (k < i + 1) = (k < i) := propext (by omega)
      simp only [e, this, ↓reduceIte]

theorem pro_ok (s₀ : State) :
    WP isa (.block mulPro) s₀ fun s => Inv s₀ (fun _ => 0) 0 s ∧ s.gpr .x12 = BitVec.ofNat 64 256 := by
  unfold mulPro
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun s₁ ⟨⟨hc, hm⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x12] (Q := fun s => s.gpr .x12 = BitVec.ofNat 64 256 ∧ s.mem = s₁.mem) (by arun)
    (by decide)) fun s₂ ⟨⟨h12, hm₂⟩, k₂⟩ => ⟨?_, h12⟩
  have k := k₁.trans k₂
  refine ⟨by rw [k.get .x0, coeffAddr, Nat.mul_zero, BitVec.add_zero],
    by rw [k.get .x1, coeffAddr, Nat.mul_zero, BitVec.add_zero],
    by rw [k.get .x2, coeffAddr, Nat.mul_zero, BitVec.add_zero],
    ⟨by rw [k₂.get .x9, hc.x9], by rw [k₂.get .x10, hc.x10], by rw [k₂.get .x11, hc.x11]⟩, k.mono,
    by rw [hm₂, hm]; exact Frame.refl _ _, fun k _ => by rw [hm₂, hm]; rfl⟩

/-- The whole function, with a body that stores `v i` to coefficient `i`,
where `v i` is coefficient `i` of the result. -/
theorem fn_ok {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} {s₀ : State} {body : List Instr}
    {v : Nat → BitVec 32} (hbody : BodyOk s₀ body v)
    (hv : ∀ i < 256, (v i).toNat = ((t (polyAt s₀.mem (s₀.gpr .x0)) (polyAt s₀.mem (s₀.gpr .x1))
      (polyAt s₀.mem (s₀.gpr .x2)))[i]!).val)
    (hpres : (Code.seq (.block mulPro) (.loop (.block body) (.nonzero .x .x12)) : Prog isa).allInstrs
      (keeps (RegSet.ofList preserved)) = true)
    (hvec : (Code.seq (.block mulPro) (.loop (.block body) (.nonzero .x .x12)) : Prog isa).allInstrs keepsV = true := by decide +kernel) :
    ∃ tr s', Exec isa (.seq (.block mulPro) (.loop (.block body) (.nonzero .x .x12))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (mulK t hPre).post s₀ s' := by
  obtain ⟨tr, s', he, hI⟩ := WP.seq (M := isa) (WP.mono (pro_ok s₀) fun s ⟨h0, hc⟩ =>
    wp_countdown (cnt := .x12) (N := 256) (by decide) (by decide) (Inv s₀ v) (fun i hi s hI _ =>
      WP.mono (hbody i hi s hI) fun s' ⟨⟨hm, h0, h1, h2, hc⟩, hk⟩ => ⟨inv_step hi hI hm h0 h1 h2 hk, hc⟩)
      (show Inv s₀ v 0 s from ⟨h0.x0, h0.x1, h0.x2, h0.consts, h0.keep, h0.frame, fun k hk => by
        rw [h0.coeff k hk]; rfl⟩) hc)
  refine ⟨tr, s', he, VG.Proof.MlKem.AArch64.abi_of rfl hpres he hvec,
    polyIs_of_toNat fun i hi => by rw [hI.coeff i hi, ite_eq_left hi]; exact hv i hi⟩

end Mul

/-! ## The functions -/

theorem mul_correct (s : State) (hs : (mulK (fun _ f g => Spec.MlDsa.multiplyNTT f g) fun _ _ => True).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.mul s t s' ∧ abiPreserved s s' ∧
      (mulK (fun _ f g => Spec.MlDsa.multiplyNTT f g) fun _ _ => True).post s s' :=
  Mul.fn_ok (v := fun i => (redX (w64 (coeffAt s.mem (s.gpr .x1) i) * w64 (coeffAt s.mem (s.gpr .x2) i))).setWidth 32)
    (fun i hi s' hI => by
      obtain ⟨-, e1, e2, h0, -, h1, h2⟩ := Mul.reads hs hi hI
      have := mulBody_ok s' hI.consts h0 h1 h2
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [mul_get _ _ hi]
      exact redX_mulW (polyAt_val hs.2.2.2.2.2.1 hi).symm (polyAt_val hs.2.2.2.2.2.2 hi).symm)
    (by decide +kernel)

theorem mulAdd_correct (s : State)
    (hs : (mulK (fun h f g => Spec.MlDsa.add h (Spec.MlDsa.multiplyNTT f g)) Reduced).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.mulAdd s t s' ∧ abiPreserved s s' ∧
      (mulK (fun h f g => Spec.MlDsa.add h (Spec.MlDsa.multiplyNTT f g)) Reduced).post s s' :=
  Mul.fn_ok (v := fun i => (redX (w64 (coeffAt s.mem (s.gpr .x1) i) * w64 (coeffAt s.mem (s.gpr .x2) i) +
      w64 (coeffAt s.mem (s.gpr .x0) i))).setWidth 32)
    (fun i hi s' hI => by
      obtain ⟨e0, e1, e2, h0, h0', h1, h2⟩ := Mul.reads hs hi hI
      have := mulAddBody_ok s' hI.consts h0 h0' h1 h2
      rwa [e0, e1, e2] at this)
    (fun i hi => by
      rw [add_get _ _ hi, mul_get _ _ hi]
      exact redX_mulAddW (polyAt_val hs.2.2.2.2.2.1 hi).symm (polyAt_val hs.2.2.2.2.2.2 hi).symm
        (polyAt_val hs.2.2.2.2.1 hi).symm)
    (by decide +kernel)

theorem mul_agree {t : Poly → Poly → Poly → Poly} {hPre : Mem → Addr → Prop} (s₁ s₂ : State)
    (_ : (mulK t hPre).pre s₁) (_ : (mulK t hPre).pre s₂) (hp : (mulK t hPre).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ :=
  agree_regs hp.2.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1]

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.mul (Spec.MlDsa.mulContract AArch64.abi) :=
  Verified.of_correct mul_correct
    (VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2]) mul_agree (by taint_decide))
    (by mldsa_implies [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, mulK, AArch64.abi, AArch64.argRegs]
      [mulSat] using mulSat)

theorem mulAdd_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.mulAdd (Spec.MlDsa.mulAddContract AArch64.abi) :=
  Verified.of_correct mulAdd_correct
    (VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2]) mul_agree (by taint_decide))
    (by mldsa_implies [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, mulK, AArch64.abi, AArch64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.AArch64.Arith
