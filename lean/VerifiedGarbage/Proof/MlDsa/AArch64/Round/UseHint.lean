import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt

/-!
# ML-DSA on AArch64: `vg_mldsa_use_hint`

Untrusted: everything here is checked by Lean. The body computes
`(f + m + δ) mod m` (`uhV`): `δ` is `2s - 1` for the sign bit `s` of
`f · 2γ₂ - a`, times the sign bit of `0 - h` (whether the hint is 1), and
two conditional subtractions of `m` reduce `f + m + δ < 3m` (`csubM_toNat`).
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Impl.MlDsa.AArch64.Arith (movW)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- `v` less `m` if that is not negative (`csubR`). -/
def csubM (m : BitVec 64) (v : BitVec 64) : BitVec 64 := v - m + ((v - m) >>> 63) * m

/-- The value the body stores, from `a` and the hint's word `h`. -/
def uhV (g : Nat) (a h : BitVec 64) : BitVec 64 :=
  csubM (BitVec.ofNat 64 (dMod g)) (csubM (BitVec.ofNat 64 (dMod g))
    (((fX g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 - BitVec.ofNat 64 1) * ((0 - h) >>> 63) + fX g a +
      BitVec.ofNat 64 (dMod g)))

theorem uhBody_ok (g : Nat) (s : State) (hM : s.gpr .x5 = BitVec.ofNat 64 (hbMul g))
    (hA : s.gpr .x6 = BitVec.ofNat 64 (hbAdd g)) (h7 : s.gpr .x7 = BitVec.ofNat 64 (2 * g))
    (h9 : s.gpr .x9 = 0) (h10 : s.gpr .x10 = BitVec.ofNat 64 (dMod g))
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4)
    (h3 : InRegions s.wr (s.gpr .x3) 4) :
    WP isa (.block (uhBody g ++ [Reg.x0, .x1, .x3].map (fun p => .addImm .x p p 4) ++
      [.subImm .x .x8 .x8 1])) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x3) ((uhV g ((s.mem.readW (s.gpr .x1) 32).setWidth 64)
          ((s.mem.readW (s.gpr .x0) 32).setWidth 64)).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 4 ∧ s'.gpr .x8 = s.gpr .x8 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x1, .x3, .x8, .x11, .x12, .x13, .x14] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold uhBody hbRaw csubR
  have hS := @dShift_lt g
  have hm := @dMod_lt g
  arun [h0, h1, h3, hM, hA, h7, h9, h10, hS, hm, uhV, csubM, fX, List.map_cons, List.map_nil]

/-! ## The values -/

theorem csubM_toNat {m : Nat} (hm : m < 2 ^ 32) {v : BitVec 64} (hv : v.toNat < 2 ^ 32) :
    (csubM (BitVec.ofNat 64 m) v).toNat = if v.toNat < m then v.toNat else v.toNat - m := by
  have hmv : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
  unfold csubM
  rw [sgn_sub (by omega) (by rw [hmv]; omega), hmv, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, hmv]
  by_cases h : v.toNat < m
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [bitV, Bool.toNat_true, BitVec.toNat_ofNat]
    omega
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp only [bitV, Bool.toNat_false, BitVec.toNat_ofNat]
    omega

theorem uhV_toNat {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat < q) :
    ((uhV g (a.setWidth 64) (h.setWidth 64)).setWidth 32).toNat =
      (if decide (h ≠ 0) then (if hbF g a.toNat * (2 * g) < a.toNat then hbF g a.toNat + hbM g + 1
        else hbF g a.toNat + hbM g - 1) else hbF g a.toNat + hbM g) % hbM g := by
  have hq : q = 8380417 := rfl
  have ha' : (a.setWidth 64).toNat < q := by rw [toNat_setWidth64]; exact ha
  have hf := fX_toNat hg ha'
  rw [toNat_setWidth64] at hf
  have hle := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm44 : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have hm16 : 16 ≤ hbM g := by rcases hg with rfl | rfl <;> decide
  have hg2 : 2 * g ≤ 523776 := by rcases hg with rfl | rfl <;> decide
  have hdm : dMod g = hbM g := dMod_eq hg
  generalize hF : hbF g a.toNat = F at hf hle
  have hfg : (fX g (a.setWidth 64) * BitVec.ofNat 64 (2 * g)).toNat = F * (2 * g) := by
    rw [BitVec.toNat_mul, hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * g) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ (Nat.lt_succ_of_le
      (Nat.le_trans hle hm44))) hg2) (by decide))
  have hs := sgn_sub (x := fX g (a.setWidth 64) * BitVec.ofNat 64 (2 * g)) (y := a.setWidth 64)
    (by rw [hfg]; have := Nat.mul_le_mul (Nat.le_trans hle hm44) hg2; omega)
    (by rw [toNat_setWidth64]; omega)
  have hh := sgn_sub (x := 0) (y := h.setWidth 64) (by decide)
    (by rw [toNat_setWidth64]; have := h.isLt; omega)
  rw [hfg, toNat_setWidth64] at hs
  rw [toNat_setWidth64] at hh
  have hne : decide (h ≠ 0) = decide ((0 : BitVec 64).toNat < h.toNat) := by
    refine decide_eq_decide.mpr ⟨fun h' => ?_, fun h' e => ?_⟩
    · have : h.toNat ≠ 0 := fun e => h' (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      show 0 < h.toNat; omega
    · rw [e] at h'; exact absurd h' (by decide)
  unfold uhV
  rw [hs, hh, ← hne]
  have hM : (BitVec.ofNat 64 (dMod g)).toNat = hbM g := by rw [BitVec.toNat_ofNat, hdm]; omega
  -- The value before the reductions: `F + m + δ`.
  have hv : ((((bitV (decide (F * (2 * g) < a.toNat)) <<< 1) - BitVec.ofNat 64 1) * bitV (decide (h ≠ 0)) +
      fX g (a.setWidth 64) + BitVec.ofNat 64 (dMod g))).toNat =
      if decide (h ≠ 0) then (if F * (2 * g) < a.toNat then F + hbM g + 1 else F + hbM g - 1) else F + hbM g := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hf, hM]
    cases decide (h ≠ 0) <;> cases hc : decide (F * (2 * g) < a.toNat)
    · simp only [Bool.false_eq_true, ite_false]; rw [show (bitV false <<< 1 - BitVec.ofNat 64 1) * bitV false = 0
        from by decide]; simp; omega
    · simp only [Bool.false_eq_true, ite_false]; rw [show (bitV true <<< 1 - BitVec.ofNat 64 1) * bitV false = 0
        from by decide]; simp; omega
    · have : ¬ F * (2 * g) < a.toNat := by simpa using hc
      simp only [ite_true, ite_eq_right_iff.mpr (fun h => absurd h this)]
      rw [show (bitV false <<< 1 - BitVec.ofNat 64 1) * bitV true = BitVec.allOnes 64 from by decide,
        BitVec.toNat_allOnes]
      omega
    · have : F * (2 * g) < a.toNat := by simpa using hc
      simp only [ite_true, ite_eq_left_iff.mpr (fun h => absurd this h)]
      rw [show (bitV true <<< 1 - BitVec.ofNat 64 1) * bitV true = 1 from by decide]
      rw [show (1 : BitVec 64).toNat = 1 from rfl]
      omega
  generalize ((((bitV (decide (F * (2 * g) < a.toNat)) <<< 1) - BitVec.ofNat 64 1) * bitV (decide (h ≠ 0)) +
      fX g (a.setWidth 64) + BitVec.ofNat 64 (dMod g))) = v at hv
  have hv3 : v.toNat < 3 * hbM g := by rw [hv]; (repeat' split) <;> omega
  have hv1 : v.toNat + 1 ≥ hbM g := by rw [hv]; (repeat' split) <;> omega
  have c1 := csubM_toNat (m := dMod g) (v := v) (by omega) (by omega)
  have c2 := csubM_toNat (m := dMod g) (v := csubM (BitVec.ofNat 64 (dMod g)) v) (by omega)
    (by rw [c1]; split <;> omega)
  rw [c1] at c2
  rw [BitVec.toNat_setWidth, c2, ← hv]
  generalize v.toNat = V at *
  rw [hdm]
  have e : V % hbM g = if V < hbM g then V else if V < 2 * hbM g then V - hbM g else V - 2 * hbM g := by
    rcases hg with rfl | rfl <;> simp only [show hbM g32 = 16 from rfl, show hbM g88 = 44 from rfl] at * <;>
      (repeat' split) <;> omega
  rw [e]
  by_cases h1 : V < hbM g
  · simp only [h1, ite_true]; omega
  · simp only [h1, ite_false]
    by_cases h2 : V - hbM g < hbM g
    · have h2' : V < 2 * hbM g := by omega
      simp only [h2, h2', ite_true]; omega
    · have h2' : ¬ V < 2 * hbM g := by omega
      simp only [h2, h2', ite_false]; omega

/-! ## The function -/

/-- The constants of `useHint`. -/
def uhCv (g : Nat) (r : Reg) : BitVec 64 :=
  if r = .x5 then BitVec.ofNat 64 (hbMul g) else if r = .x6 then BitVec.ofNat 64 (hbAdd g)
  else if r = .x7 then BitVec.ofNat 64 (2 * g) else if r = .x9 then 0 else BitVec.ofNat 64 (dMod g)

theorem uhConsts_ok (g : Nat) (hg : IsG g) (s : State) :
    WP isa (.block (uhConsts g)) s fun s' =>
      ((∀ r ∈ [Reg.x5, .x6, .x7, .x9, .x10], s'.gpr r = uhCv g r) ∧ s'.mem = s.mem ∧
        (∀ s'', s''.mem = s'.mem → Keep [.x8] s' s'' → True)) ∧ Keep [.x5, .x6, .x7, .x9, .x10] s s' := by
  unfold uhConsts
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (hbConsts_ok g hg .x5 .x6 (by decide) s) fun s₁ ⟨⟨h5, h6, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x7 _ s₁) fun s₂ ⟨⟨h7, hm₂⟩, k₂⟩ => ?_
  have hdm : dMod g < 65536 := by rcases hg with rfl | rfl <;> decide
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x9, .x10] (Q := fun s' => s'.gpr .x9 = 0 ∧
    s'.gpr .x10 = BitVec.ofNat 64 (dMod g) ∧ s'.mem = s₂.mem) (by arun [VG.Proof.MlDsa.AArch64.Arith.imm16 hdm])
    (by rfl)) fun s₃ ⟨⟨h9, h10, hm₃⟩, k₃⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm₃, hm₂, hm₁], fun _ _ _ => trivial⟩, ((k₁.trans k₂).trans k₃).mono⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [k₃.get .x5, k₂.get .x5, h5]; rfl
  · rw [k₃.get .x6, k₂.get .x6, h6]; rfl
  · rw [k₃.get .x7, h7]; rcases hg with rfl | rfl <;> decide
  · rw [h9]; rfl
  · rw [h10]; rfl

theorem useHint_body (s₀ : State) :
    GBody (zextS .x2 s₀) [.x0, .x1, .x3] [.x5, .x6, .x7, .x9, .x10] [.x3]
      [.x0, .x1, .x3, .x8, .x11, .x12, .x13, .x14] .x8 uhCv
      (fun g _ i => (uhV g ((coeffAt s₀.mem (s₀.gpr .x1) i).setWidth 64)
        ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64)).setWidth 32) (fun _ _ _ => True) [.x0, .x1] uhBody := by
  intro g _ sL hL hcv hmL he i hi s hI
  have hc : ∀ r ∈ [Reg.x5, .x6, .x7, .x9, .x10], s.gpr r = uhCv g r := fun r hr => by
    rw [hI.fixed r hr, hcv r hr]
  have e0 : s.mem.readW (s.gpr .x0) 32 = coeffAt s₀.mem (s₀.gpr .x0) i := by
    rw [hI.read hL (by simp) (by simp) hi, hmL, he .x0 (by simp), zextS_mem, zextS_other s₀ (by decide)]
  have e1 : s.mem.readW (s.gpr .x1) 32 = coeffAt s₀.mem (s₀.gpr .x1) i := by
    rw [hI.read hL (by simp) (by simp) hi, hmL, he .x1 (by simp), zextS_mem, zextS_other s₀ (by decide)]
  refine WP.mono (uhBody_ok g s (hc .x5 (by simp)) (hc .x6 (by simp)) (hc .x7 (by simp)) (hc .x9 (by simp))
    (hc .x10 (by simp)) (hI.inR hL (by simp) (by simp) hi) (hI.inR hL (by simp) (by simp) hi)
    (hI.inW hL (by simp) (by simp) hi))
    fun s' ⟨⟨hm', h0, h1, h3, hc'⟩, hk'⟩ => ⟨⟨?_, fun p hp' => ?_, hc', trivial⟩, hk'⟩
  · rw [hm', e0, e1]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    exacts [h0, h1, h3]

theorem useHint_correct (s₀ : State) (hp : useHintK.pre s₀) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Round.useHint s₀ t s' ∧ abiPreserved s₀ s' ∧ useHintK.post s₀ s' := by
  have hr1 : Reduced s₀.mem (s₀.gpr .x1) := hp.2.2.2.2.2
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
  obtain ⟨t, s', he, sL, hk, hm, hI⟩ := zext_ok (gamma_ok (gr := .x2) (t := .x4) (ins := [.x0, .x1])
    (outs := [.x3]) (fixed := [.x5, .x6, .x7, .x9, .x10]) (kc := [.x5, .x6, .x7, .x9, .x10]) hg hL (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun g hg s => uhConsts_ok g hg s)
    (useHint_body s₀))
  have k1 := (zextS_keep .x2 s₀).trans hk
  have e3 : sL.gpr .x3 = s₀.gpr .x3 := k1.get .x3
  rw [zextS_toNat] at hI
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, ?_⟩
  refine natPolyIs_of_toNat fun k hk' => ?_
  rw [← e3, hI.done .x3 (by simp) k hk', zipWith_get _ _ _ hk', hintAt_get _ _ hk',
    useHint_eq hp.2.2.2.2.1, uhV_toNat (isG_of_mem hp.2.2.2.2.1) (hr1 k hk'), polyAt_val hr1 hk']
  exact (Int.toNat_natCast _).symm

theorem useHint_ct : ConstantTime isa useHintK.pre useHintK.pub Impl.MlDsa.AArch64.Round.useHint := by
  unfold Impl.MlDsa.AArch64.Round.useHint
  refine zext_ct (τ := VG.AArch64.Taint.ofRegs [.x2, .x0, .x1, .x3])
    (fun _ _ hp => agree_zext hp.2.2.2.2 hp.2.2.1 fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hp.1, hp.2.1, hp.2.2.2.1]

theorem useHint_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Round.useHint (useHintContract AArch64.abi) :=
  Verified.of_correct useHint_correct useHint_ct (by
    mldsa_implies [useHintContract, useHintSig, useHintK, hintK, AArch64.abi, AArch64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.AArch64.Round
