import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-!
# ML-DSA on AArch64: `vg_mldsa_add` and `vg_mldsa_sub`

Untrusted: everything here is checked by Lean. The body stores the value
`v i` to coefficient `i` of `f` (`addBody_ok`, `subBody_ok`); the loop is
proven once for any such body (`AddSub.fn_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## One coefficient -/

/-- A word, zero-extended. -/
abbrev w64 (v : BitVec 32) : BitVec 64 := v.setWidth 64

theorem addBody_ok (s : State) (hq : s.gpr .x9 = Qv) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h3 : InRegions s.wr (s.gpr .x0) 4) :
    WP isa (.block addBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0)
          ((csubX (w64 (s.mem.readW (s.gpr .x0) 32) + w64 (s.mem.readW (s.gpr .x1) 32))).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x10 = s.gpr .x10 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x10, .x11, .x12] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold addBody Impl.MlKem.AArch64.csub step2
  arun [h1, h2, h3, hq, csubX]

theorem subBody_ok (s : State) (hq : s.gpr .x9 = Qv) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h3 : InRegions s.wr (s.gpr .x0) 4) :
    WP isa (.block subBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0)
          ((csubX (w64 (s.mem.readW (s.gpr .x0) 32) + Qv - w64 (s.mem.readW (s.gpr .x1) 32))).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x10 = s.gpr .x10 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x10, .x11, .x12] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold subBody Impl.MlKem.AArch64.csub step2
  arun [h1, h2, h3, hq, csubX]

/-! ## The loop -/

theorem coeffAddr_next (p : Addr) (j : Nat) : coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) :=
  coeffAddr_add p j 1

namespace AddSub

/-- After `i` coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = coeffAddr (s₀.gpr .x0) i
  x1 : s.gpr .x1 = coeffAddr (s₀.gpr .x1) i
  x9 : s.gpr .x9 = Qv
  keep : Keep [.x0, .x1, .x9, .x10, .x11, .x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .x0) k = if k < i then v k else coeffAt s₀.mem (s₀.gpr .x0) k

/-- The body stores `v i` to coefficient `i`. -/
def BodyOk (s₀ : State) (body : List Instr) (v : Nat → BitVec 32) : Prop :=
  ∀ i < 256, ∀ s, Inv s₀ v i s → WP isa (.block body) s fun s' =>
    (s'.mem = s.mem.writeW (s.gpr .x0) (v i) ∧ s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧ s'.gpr .x10 = s.gpr .x10 - BitVec.ofNat 64 1) ∧
    Keep [.x0, .x1, .x10, .x11, .x12] s s'

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
include hp

/-- The accesses of iteration `i`, and the words it reads. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s : State} (hI : Inv s₀ v i s) :
    s.mem.readW (s.gpr .x0) 32 = coeffAt s₀.mem (s₀.gpr .x0) i ∧
      s.mem.readW (s.gpr .x1) 32 = coeffAt s₀.mem (s₀.gpr .x1) i ∧
      InRegions (s.rd ++ s.wr) (s.gpr .x0) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .x1) 4 ∧
      InRegions s.wr (s.gpr .x0) 4 := by
  have hrd : s.rd = [pR (s₀.gpr .x1)] := hI.keep.rd.trans hp.1
  have hwr : s.wr = [pR (s₀.gpr .x0)] := hI.keep.wr.trans hp.2.1
  rw [hI.x0, hI.x1, hrd, hwr]
  refine ⟨?_, ?_, ⟨_, by simp, coeff_contains _ hi⟩, ⟨_, by simp, coeff_contains _ hi⟩,
    ⟨_, by simp, coeff_contains _ hi⟩⟩
  · rw [← coeffAt_eq, hI.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · rw [← coeffAt_eq]
    exact coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) hi

omit hp in
theorem inv_step {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s s' : State} (hI : Inv s₀ v i s)
    (hm : s'.mem = s.mem.writeW (s.gpr .x0) (v i)) (h0 : s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4)
    (h1 : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4) (hk : Keep [.x0, .x1, .x10, .x11, .x12] s s') :
    Inv s₀ v (i + 1) s' where
  x0 := by rw [h0, hI.x0, coeffAddr_next]
  x1 := by rw [h1, hI.x1, coeffAddr_next]
  x9 := by rw [hk.get .x9, hI.x9]
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

omit hp in
theorem pro_ok :
    WP isa (.block accPro) s₀ fun s => Inv s₀ (fun _ => 0) 0 s ∧ s.gpr .x10 = BitVec.ofNat 64 256 := by
  unfold accPro
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x9 _ s₀) fun s₁ ⟨⟨h9, hm⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x10] (Q := fun s => s.gpr .x10 = BitVec.ofNat 64 256 ∧ s.mem = s₁.mem) (by arun)
    (by decide)) fun s₂ ⟨⟨h10, hm₂⟩, k₂⟩ => ⟨?_, h10⟩
  have k := k₁.trans k₂
  refine ⟨by rw [k.get .x0, coeffAddr, Nat.mul_zero, BitVec.add_zero],
    by rw [k.get .x1, coeffAddr, Nat.mul_zero, BitVec.add_zero], by rw [k₂.get .x9, h9]; exact q32, k.mono,
    by rw [hm₂, hm]; exact Frame.refl _ _, fun k _ => by rw [hm₂, hm]; rfl⟩

omit hp in
/-- The whole function, from its precondition, with a body that stores `v i`
to coefficient `i`, where `v i` is coefficient `i` of the result. -/
theorem fn_ok {body : List Instr} {v : Nat → BitVec 32} (hbody : BodyOk s₀ body v)
    (hv : ∀ i < 256, (v i).toNat = ((t (polyAt s₀.mem (s₀.gpr .x0)) (polyAt s₀.mem (s₀.gpr .x1)))[i]!).val)
    (hpres : (Code.seq (.block accPro) (.loop (.block body) (.nonzero .x .x10)) : Prog isa).allInstrs
      (keeps (RegSet.ofList preserved)) = true) :
    ∃ tr s', Exec isa (.seq (.block accPro) (.loop (.block body) (.nonzero .x .x10))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  obtain ⟨tr, s', he, hI⟩ := WP.seq (M := isa) (WP.mono pro_ok fun s ⟨h0, hc⟩ =>
    wp_countdown (cnt := .x10) (N := 256) (by decide) (by decide) (Inv s₀ v) (fun i hi s hI _ =>
      WP.mono (hbody i hi s hI) fun s' ⟨⟨hm, h0, h1, hc⟩, hk⟩ => ⟨inv_step hi hI hm h0 h1 hk, hc⟩)
      (show Inv s₀ v 0 s from ⟨h0.x0, h0.x1, h0.x9, h0.keep, h0.frame, fun k hk => by
        rw [h0.coeff k hk]; rfl⟩) hc)
  refine ⟨tr, s', he, VG.Proof.MlKem.AArch64.abi_of rfl hpres he,
    polyIs_of_toNat fun i hi => by rw [hI.coeff i hi, ite_eq_left hi]; exact hv i hi⟩

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.add s t s' ∧ abiPreserved s s' ∧
      (accK Spec.MlDsa.add).post s s' :=
  AddSub.fn_ok (v := fun i => (csubX (w64 (coeffAt s.mem (s.gpr .x0) i) +
      w64 (coeffAt s.mem (s.gpr .x1) i))).setWidth 32)
    (fun i hi s' hI => by
      obtain ⟨e1, e2, h1, h2, h3⟩ := AddSub.reads hs hi hI
      have := addBody_ok s' hI.x9 h1 h2 h3
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [add_get _ _ hi]
      exact csubX_add (polyAt_val hs.2.2.2.1 hi).symm (polyAt_val hs.2.2.2.2 hi).symm)
    (by decide +kernel)

theorem sub_correct (s : State) (hs : (accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.sub s t s' ∧ abiPreserved s s' ∧
      (accK Spec.MlDsa.sub).post s s' :=
  AddSub.fn_ok (v := fun i => (csubX (w64 (coeffAt s.mem (s.gpr .x0) i) + Qv -
      w64 (coeffAt s.mem (s.gpr .x1) i))).setWidth 32)
    (fun i hi s' hI => by
      obtain ⟨e1, e2, h1, h2, h3⟩ := AddSub.reads hs hi hI
      have := subBody_ok s' hI.x9 h1 h2 h3
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [sub_get _ _ hi]
      exact csubX_sub (polyAt_val hs.2.2.2.1 hi).symm (polyAt_val hs.2.2.2.2 hi).symm)
    (by decide +kernel)

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1]) s₁ s₂ :=
  agree_regs hp.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.1]

theorem add_ct :
    ConstantTime isa (accK Spec.MlDsa.add).pre (accK Spec.MlDsa.add).pub Impl.MlDsa.AArch64.Arith.add :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) acc_agree (by taint_decide)

theorem sub_ct :
    ConstantTime isa (accK Spec.MlDsa.sub).pre (accK Spec.MlDsa.sub).pub Impl.MlDsa.AArch64.Arith.sub :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) acc_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.add (Spec.MlDsa.addContract AArch64.abi) :=
  Verified.of_correct add_correct add_ct (by
    mldsa_implies [Spec.MlDsa.addContract, Spec.MlDsa.accSig, accK, AArch64.abi, AArch64.argRegs]
      [accSat] using accSat)

theorem sub_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.sub (Spec.MlDsa.subContract AArch64.abi) :=
  Verified.of_correct sub_correct sub_ct (by
    mldsa_implies [Spec.MlDsa.subContract, Spec.MlDsa.accSig, accK, AArch64.abi, AArch64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlDsa.AArch64.Arith
