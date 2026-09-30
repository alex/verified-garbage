import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.Round.Ones

/-!
# ML-DSA on AArch64: `vg_mldsa_make_hint`

Untrusted: everything here is checked by Lean. The hint is whether `r₁` of
`r` and of `r + z mod q` differ: their xor, less than 64, is nonzero
(`hbit_toNat`); `x8` counts the 1s (`J`, `onesTo`).
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok csubX csubX_toNat)
open VG.Impl.MlDsa.AArch64.Arith (movW)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- The hint the body computes of `r` and `z`: 1 if `r₁` of `r` and of
`r + z mod q` differ, else 0. -/
def hbit (g : Nat) (r z : BitVec 64) : BitVec 64 := ((r1X g (csubX (r + z)) ^^^ r1X g r) + BitVec.ofNat 64 63) >>> 6

theorem mhBody_ok (g : Nat) (s : State) (hM : s.gpr .x5 = BitVec.ofNat 64 (hbMul g))
    (hA : s.gpr .x6 = BitVec.ofNat 64 (hbAdd g)) (hq : s.gpr .x9 = Qv)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4)
    (h3 : InRegions s.wr (s.gpr .x3) 4) :
    WP isa (.block (mhBody g ++ [Reg.x0, .x1, .x3].map (fun p => .addImm .x p p 4) ++
      ([.subImm .x .x7 .x7 1] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x3) ((hbit g ((s.mem.readW (s.gpr .x1) 32).setWidth 64)
          ((s.mem.readW (s.gpr .x0) 32).setWidth 64)).setWidth 32) ∧
        s'.gpr .x8 = s.gpr .x8 + hbit g ((s.mem.readW (s.gpr .x1) 32).setWidth 64)
          ((s.mem.readW (s.gpr .x0) 32).setWidth 64) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 4 ∧ s'.gpr .x7 = s.gpr .x7 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x3, .x7, .x8, .x11, .x12, .x13, .x14] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold mhBody hb hbRaw Impl.MlKem.AArch64.csub
  have hS := @dShift_lt g
  have hm := @dMod_lt g
  arun [h0, h1, h3, hM, hA, hq, hS, hm, hbit, r1X, fX, csubX, List.map_cons, List.map_nil]

/-! ## The values -/

theorem xor_lt64 {x y : BitVec 64} (hx : x.toNat < 64) (hy : y.toNat < 64) : (x ^^^ y).toNat < 64 := by
  rw [BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow (n := 6) hx hy

theorem hbit_toNat {g : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (hbit g (a.setWidth 64) (b.setWidth 64)).toNat =
      (decide (hbF g a.toNat % hbM g ≠ hbF g ((a.toNat + b.toNat) % q) % hbM g)).toNat := by
  have hq : q = 8380417 := rfl
  have ha' : (a.setWidth 64).toNat < q := by rw [toNat_setWidth64]; exact ha
  have e : (a.setWidth 64 + b.setWidth 64).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, toNat_setWidth64, toNat_setWidth64]; omega
  have hc : (csubX (a.setWidth 64 + b.setWidth 64)).toNat = (a.toNat + b.toNat) % q := by
    rw [csubX_toNat (by rw [e]; omega), e, VG.Proof.MlDsa.Arith.condSub_eq (by omega)]
  have hc' : (csubX (a.setWidth 64 + b.setWidth 64)).toNat < q := by rw [hc]; exact Nat.mod_lt _ (by decide)
  have hm44 : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have l1 := r1X_lt hg hc'
  have l2 := r1X_lt hg ha'
  have v1 := r1X_toNat hg hc'
  have v2 := r1X_toNat hg ha'
  rw [hc] at v1
  rw [toNat_setWidth64] at v2
  have hx := xor_lt64 (x := r1X g (csubX (a.setWidth 64 + b.setWidth 64))) (y := r1X g (a.setWidth 64))
    (by omega) (by omega)
  have hxz : (r1X g (csubX (a.setWidth 64 + b.setWidth 64)) ^^^ r1X g (a.setWidth 64)).toNat = 0 ↔
      hbF g a.toNat % hbM g = hbF g ((a.toNat + b.toNat) % q) % hbM g := by
    rw [← v1, ← v2]
    generalize r1X g (csubX (a.setWidth 64 + b.setWidth 64)) = X
    generalize r1X g (a.setWidth 64) = Y
    constructor
    · intro h
      have h0 : X ^^^ Y = 0 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have := congrArg (· ^^^ Y) h0
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      rw [this, BitVec.toNat_xor]
      simp
    · intro h
      rw [BitVec.toNat_eq.mpr h.symm, BitVec.xor_self]; rfl
  unfold hbit
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases h : hbF g a.toNat % hbM g = hbF g ((a.toNat + b.toNat) % q) % hbM g
  · rw [decide_eq_false (Classical.not_not.mpr h), hxz.mpr h]; rfl
  · rw [decide_eq_true h]
    have := mt hxz.mp h
    simp only [Bool.toNat_true]
    omega

/-! ## The function -/

/-- The constants of `makeHint`. -/
def mhCv (g : Nat) (r : Reg) : BitVec 64 :=
  if r = .x5 then BitVec.ofNat 64 (hbMul g) else if r = .x6 then BitVec.ofNat 64 (hbAdd g) else Qv

/-- The hint of the polynomials at `z = x0` and `r = x1`. -/
def hintOf (s₀ : State) (g : Nat) : Vector Bool n :=
  Vector.zipWith (makeHint g) (polyAt s₀.mem (s₀.gpr .x0)) (polyAt s₀.mem (s₀.gpr .x1))

/-- The count of 1s in `x8` after `i` coefficients. -/
def mhJ (s₀ : State) (g i : Nat) (s : State) : Prop := (s.gpr .x8).toNat = onesTo (hintOf s₀ g) i

theorem mhConsts_ok (s₀ : State) (g : Nat) (hg : IsG g) (s : State) :
    WP isa (.block (mhConsts g)) s fun s' =>
      ((∀ r ∈ [Reg.x5, .x6, .x9], s'.gpr r = mhCv g r) ∧ s'.mem = s.mem ∧
        (∀ s'', s''.mem = s'.mem → Keep [.x7] s' s'' → mhJ s₀ g 0 s'')) ∧ Keep [.x5, .x6, .x9, .x8] s s' := by
  unfold mhConsts
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (hbConsts_ok g hg .x5 .x6 (by decide) s) fun s₁ ⟨⟨h5, h6, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x9 _ s₁) fun s₂ ⟨⟨h9, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x8] (Q := fun s' => s'.gpr .x8 = 0 ∧ s'.mem = s₂.mem)
    (by arun) (by rfl)) fun s₃ ⟨⟨h8, hm₃⟩, k₃⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm₃, hm₂, hm₁], fun s'' _ hk => ?_⟩, ((k₁.trans k₂).trans k₃).mono⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [k₃.get .x5, k₂.get .x5, h5]; rfl
    · rw [k₃.get .x6, k₂.get .x6, h6]; rfl
    · rw [k₃.get .x9, h9]; exact q32
  · show (s''.gpr .x8).toNat = _
    rw [hk.get .x8, h8, onesTo_zero]; rfl

theorem makeHint_body (s₀ : State) (hr0 : Reduced s₀.mem (s₀.gpr .x0)) (hr1 : Reduced s₀.mem (s₀.gpr .x1)) :
    GBody (zextS .x2 s₀) [.x0, .x1, .x3] [.x5, .x6, .x9] [.x3] [.x0, .x1, .x3, .x7, .x8, .x11, .x12, .x13, .x14]
      .x7 mhCv (fun g _ i => (hbit g ((coeffAt s₀.mem (s₀.gpr .x1) i).setWidth 64)
        ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64)).setWidth 32) (mhJ s₀) [.x0, .x1] mhBody := by
  intro g hg sL hL hcv hmL he i hi s hI
  have hc : ∀ r ∈ [Reg.x5, .x6, .x9], s.gpr r = mhCv g r := fun r hr => by rw [hI.fixed r hr, hcv r hr]
  have e0 : s.mem.readW (s.gpr .x0) 32 = coeffAt s₀.mem (s₀.gpr .x0) i := by
    rw [hI.read hL (by simp) (by simp) hi, hmL, he .x0 (by simp), zextS_mem, zextS_other s₀ (by decide)]
  have e1 : s.mem.readW (s.gpr .x1) 32 = coeffAt s₀.mem (s₀.gpr .x1) i := by
    rw [hI.read hL (by simp) (by simp) hi, hmL, he .x1 (by simp), zextS_mem, zextS_other s₀ (by decide)]
  refine WP.mono (mhBody_ok g s (hc .x5 (by simp)) (hc .x6 (by simp)) (hc .x9 (by simp))
    (hI.inR hL (by simp) (by simp) hi) (hI.inR hL (by simp) (by simp) hi) (hI.inW hL (by simp) (by simp) hi))
    fun s' ⟨⟨hm', h8, h0, h1, h3, hc'⟩, hk'⟩ => ⟨⟨?_, fun p hp' => ?_, hc', ?_⟩, hk'⟩
  · rw [hm', e0, e1]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    exacts [h0, h1, h3]
  · have hb := hbit_toNat hg (hr1 i hi) (hr0 i hi)
    have hJ : (s.gpr .x8).toNat = onesTo (hintOf s₀ g) i := hI.j
    have hle : onesTo (hintOf s₀ g) i ≤ i := by
      unfold onesTo; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have hbit1 : (hbit g ((coeffAt s₀.mem (s₀.gpr .x1) i).setWidth 64)
        ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64)).toNat = ((hintOf s₀ g)[i]!).toNat := by
      rw [hb, hintOf, zipWith_get _ _ _ hi, makeHint_eq (mem_of_isG hg), polyAt_val hr0 hi, polyAt_val hr1 hi]
    show (s'.gpr .x8).toNat = _
    rw [h8, e0, e1, BitVec.toNat_add, hbit1, hJ, onesTo_succ]
    have : ((hintOf s₀ g)[i]!).toNat ≤ 1 := Bool.toNat_le _
    omega

theorem makeHint_correct (s₀ : State) (hp : makeHintK.pre s₀) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Round.makeHint s₀ t s' ∧ abiPreserved s₀ s' ∧ makeHintK.post s₀ s' := by
  have hr0 : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2.2.2.2.1
  have hr1 : Reduced s₀.mem (s₀.gpr .x1) := hp.2.2.2.2.2.2
  have hL : Layout (zextS .x2 s₀) [.x0, .x1] [.x3] :=
    Layout.congr (s₀ := s₀)
      { rd := fun p hp' => by
          rw [hp.1]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ⊢
          rcases hp' with rfl | rfl <;> simp
        wr := fun o ho => by simp only [List.mem_singleton] at ho; subst ho; rw [hp.2.1]; simp
        dis := fun p hp' o ho => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ho; subst ho
          rcases hp' with rfl | rfl
          exacts [hp.2.2.1, hp.2.2.2.1]
        pw := List.pairwise_singleton _ _ }
      (fun r hr => zextS_other s₀ (by simp only [List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rfl rfl
  have hg : IsG ((zextS .x2 s₀).gpr .x2).toNat := by rw [zextS_toNat]; exact isG_of_mem hp.2.2.2.2.1
  have hW : WP isa Impl.MlDsa.AArch64.Round.makeHint s₀ fun s' => makeHintK.post s₀ s' := by
    refine zext_ok (WP.seq (WP.mono (gamma_ok (gr := .x2) (t := .x4) (ins := [.x0, .x1]) (outs := [.x3])
      (fixed := [.x5, .x6, .x9]) (kc := [.x5, .x6, .x9, .x8]) hg hL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun g hg s => mhConsts_ok s₀ g hg s) (makeHint_body s₀ hr0 hr1))
      fun s₂ ⟨sL, hk, hm, hI⟩ => ?_))
    have k1 := (zextS_keep .x2 s₀).trans hk
    have e3 : sL.gpr .x3 = s₀.gpr .x3 := k1.get .x3
    rw [zextS_toNat] at hI
    refine (VG.Proof.MlDsa.AArch64.Arith.WP.keep (Q := fun s3 => s3.gpr .x0 = s₂.gpr .x8 ∧ s3.mem = s₂.mem)
      [.x0] (by arun [Impl.MlKem.AArch64.mov]) (by rfl)).mono fun s3 ⟨⟨h0, hm3⟩, _⟩ => ⟨?_, ?_⟩
    · refine hintIs_of_toNat fun j hj => ?_
      rw [hm3, ← e3, hI.done .x3 (by simp) j hj]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, hbit_toNat (isG_of_mem hp.2.2.2.2.1) (hr1 j hj) (hr0 j hj),
        BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, zipWith_get _ _ _ hj, makeHint_eq hp.2.2.2.2.1,
        polyAt_val hr0 hj, polyAt_val hr1 hj]
    · have hJ : (s₂.gpr .x8).toNat = onesTo (hintOf s₀ (arg32 s₀ .x2)) 256 := hI.j
      have hle : onesTo (hintOf s₀ (arg32 s₀ .x2)) 256 ≤ 256 := by
        unfold onesTo; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      show ((s3.gpr .x0).setWidth 32).toNat = hintOnes [hintOf s₀ (arg32 s₀ .x2)]
      rw [h0, BitVec.toNat_setWidth, hJ, hintOnes_onesTo, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨t, s', he, hpost⟩ := hW
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, hpost⟩

theorem makeHint_ct : ConstantTime isa makeHintK.pre makeHintK.pub Impl.MlDsa.AArch64.Round.makeHint := by
  unfold Impl.MlDsa.AArch64.Round.makeHint
  refine zext_ct (τ := VG.AArch64.Taint.ofRegs [.x2, .x0, .x1, .x3])
    (fun _ _ hp => agree_zext hp.2.2.2.2 hp.2.2.1 fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hp.1, hp.2.1, hp.2.2.2.1]

/-- A state satisfying the preconditions of `makeHint` and `useHint`. -/
def hintSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 261888 | .x3 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem makeHint_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Round.makeHint (makeHintContract AArch64.abi) :=
  Verified.of_correct makeHint_correct makeHint_ct (by
    mldsa_implies [makeHintContract, makeHintSig, makeHintK, hintK, AArch64.abi, AArch64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.AArch64.Round
