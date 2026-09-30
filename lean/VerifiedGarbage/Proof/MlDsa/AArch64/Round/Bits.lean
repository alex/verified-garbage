import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Gamma
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round

/-!
# ML-DSA on AArch64: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-! ## The bodies -/

/-- The constants of `highBits`. -/
def hbCv (g : Nat) (r : Reg) : BitVec 64 := if r = .x4 then BitVec.ofNat 64 (hbMul g) else BitVec.ofNat 64 (hbAdd g)

theorem hbBody_ok (g : Nat) (s : State) (hM : s.gpr .x4 = BitVec.ofNat 64 (hbMul g))
    (hA : s.gpr .x5 = BitVec.ofNat 64 (hbAdd g)) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h2 : InRegions s.wr (s.gpr .x2) 4) :
    WP isa (.block (hbBody g ++ [Reg.x0, .x2].map (fun p => .addImm .x p p 4) ++ [.subImm .x .x6 .x6 1])) s
      fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x2) ((r1X g ((s.mem.readW (s.gpr .x0) 32).setWidth 64)).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧
        s'.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x2, .x6, .x11, .x12, .x13] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold hbBody hb hbRaw
  have hS := @dShift_lt g
  have hm := @dMod_lt g
  arun [h0, h2, hM, hA, hS, hm, r1X, fX, List.map_cons, List.map_nil]

theorem lbBody_ok (g : Nat) (s : State) (hM : s.gpr .x4 = BitVec.ofNat 64 (hbMul g))
    (hA : s.gpr .x5 = BitVec.ofNat 64 (hbAdd g)) (h7 : s.gpr .x7 = BitVec.ofNat 64 (2 * g))
    (hq : s.gpr .x9 = Qv) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (h2 : InRegions s.wr (s.gpr .x2) 4) :
    WP isa (.block (lbBody g ++ [Reg.x0, .x2].map (fun p => .addImm .x p p 4) ++ [.subImm .x .x6 .x6 1])) s
      fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x2) ((addQ ((s.mem.readW (s.gpr .x0) 32).setWidth 64 -
          r1X g ((s.mem.readW (s.gpr .x0) 32).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧
        s'.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x2, .x6, .x11, .x12, .x13] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold lbBody hb hbRaw
  have hS := @dShift_lt g
  have hm := @dMod_lt g
  arun [h0, h2, hM, hA, h7, hq, hS, hm, r1X, fX, addQ, List.map_cons, List.map_nil]

/-! ## The values -/

theorem hb_val {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat < q) :
    ((r1X g (a.setWidth 64)).setWidth 32).toNat = hbF g a.toNat % hbM g := by
  have h := r1X_lt hg (a := a.setWidth 64) (by rw [toNat_setWidth64]; exact ha)
  have : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), r1X_toNat hg (by rw [toNat_setWidth64]; exact ha),
    toNat_setWidth64]

theorem lb_val {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat < q) :
    ((addQ (a.setWidth 64 - r1X g (a.setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32).toNat =
      if a.toNat < hbF g a.toNat % hbM g * (2 * g) then a.toNat + q - hbF g a.toNat % hbM g * (2 * g)
      else a.toNat - hbF g a.toNat % hbM g * (2 * g) := by
  have hq : q = 8380417 := rfl
  have ha' : (a.setWidth 64).toNat < q := by rw [toNat_setWidth64]; exact ha
  have hr := r1X_toNat hg ha'
  have hlt := r1X_lt hg ha'
  rw [toNat_setWidth64] at hr
  have hmul := hbM_mul (mem_of_isG hg)
  have hg2 : 2 * g ≤ 523776 := by rcases hg with rfl | rfl <;> decide
  have hle : hbF g a.toNat % hbM g * (2 * g) ≤ q := by
    rw [← hr]
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt)
    omega
  have hk : (r1X g (a.setWidth 64) * BitVec.ofNat 64 (2 * g)).toNat = hbF g a.toNat % hbM g * (2 * g) := by
    rw [BitVec.toNat_mul, hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * g) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hv := addQ_sub_toNat (v := a.setWidth 64) (k := r1X g (a.setWidth 64) * BitVec.ofNat 64 (2 * g))
    (by rw [toNat_setWidth64]; omega) (by rw [hk]; exact hle)
  rw [hk, toNat_setWidth64] at hv
  rw [BitVec.toNat_setWidth, hv]
  split <;> omega

/-! ## The functions -/

section
variable {s₀ : State} {post : State → State → Prop} (hp : (bitsK post).pre s₀)
include hp

theorem bits_layout : Layout (zextS .x1 s₀) [.x0] [.x2] :=
  Layout.congr (s₀ := s₀)
    { rd := fun p hp' => by simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.1]; simp
      wr := fun o ho => by simp only [List.mem_singleton] at ho; subst ho; rw [hp.2.1]; simp
      dis := fun p hp' o ho => by
        simp only [List.mem_singleton] at hp' ho; subst hp' ho; exact hp.2.2.1
      pw := List.pairwise_singleton _ _ }
    (fun r hr => zextS_other s₀ (by simp only [List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide)) rfl rfl

theorem bits_g : IsG ((zextS .x1 s₀).gpr .x1).toNat := by
  rw [zextS_toNat]; exact isG_of_mem hp.2.2.2.1

end

theorem hbConsts'_ok (g : Nat) (hg : IsG g) (s : State) :
    WP isa (.block (hbConsts g .x4 .x5)) s fun s' =>
      ((∀ r ∈ [Reg.x4, .x5], s'.gpr r = hbCv g r) ∧ s'.mem = s.mem ∧
        (∀ s'', s''.mem = s'.mem → Keep [.x6] s' s'' → True)) ∧ Keep [.x4, .x5] s s' :=
  WP.mono (hbConsts_ok g hg .x4 .x5 (by decide) s) fun s' ⟨⟨h4, h5, hm⟩, hk⟩ =>
    ⟨⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h4]; rfl
      · rw [h5]; rfl, hm, fun _ _ _ => trivial⟩, hk⟩

theorem highBits_body (s₀ : State) :
    GBody (zextS .x1 s₀) [.x0, .x2] [.x4, .x5] [.x2] [.x0, .x2, .x6, .x11, .x12, .x13] .x6 hbCv
      (fun g _ i => (r1X g ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64)).setWidth 32) (fun _ _ _ => True)
      [.x0] hbBody := by
  intro g _ sL hL hcv hmL he i hi s hI
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (hbMul g) := by rw [hI.fixed .x4 (by simp), hcv .x4 (by simp)]; rfl
  have h5 : s.gpr .x5 = BitVec.ofNat 64 (hbAdd g) := by rw [hI.fixed .x5 (by simp), hcv .x5 (by simp)]; rfl
  refine WP.mono (hbBody_ok g s h4 h5 (hI.inR hL (by simp) (by simp) hi) (hI.inW hL (by simp) (by simp) hi))
    fun s' ⟨⟨hm', h0, h2, hc⟩, hk'⟩ => ⟨⟨?_, fun p hp' => ?_, hc, trivial⟩, hk'⟩
  · rw [hm', hI.read hL (by simp) (by simp) hi, hmL, he .x0 (by simp), zextS_mem, zextS_other s₀ (by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    exacts [h0, h2]

theorem highBits_correct (s₀ : State) (hp : highBitsK.pre s₀) :
    ∃ t s', Exec isa highBits s₀ t s' ∧ abiPreserved s₀ s' ∧ highBitsK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2.2.2
  obtain ⟨t, s', he, sL, hk, hm, hI⟩ := zext_ok (gamma_ok (gr := .x1) (t := .x3) (ins := [.x0])
    (outs := [.x2]) (fixed := [.x4, .x5]) (kc := [.x4, .x5]) (bits_g hp) (bits_layout hp) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun g hg s => hbConsts'_ok g hg s)
    (highBits_body s₀))
  have k1 := (zextS_keep .x1 s₀).trans hk
  have e2 : sL.gpr .x2 = s₀.gpr .x2 := k1.get .x2
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, ?_⟩
  refine natPolyIs_of_toNat fun k hk' => ?_
  rw [← e2, hI.done .x2 (by simp) k hk', zextS_toNat, map_get _ _ hk', highBits_eq hp.2.2.2.1,
    hb_val (isG_of_mem hp.2.2.2.1) (hr k hk'), polyAt_val hr hk']
  exact (Int.toNat_natCast _).symm

theorem bits_agree {post : State → State → Prop} (s₁ s₂ : State) (hp : (bitsK post).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x1, .x0, .x2]) (zextS .x1 s₁) (zextS .x1 s₂) :=
  agree_zext hp.2.2.2 hp.2.1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.2.1]

theorem highBits_ct : ConstantTime isa highBitsK.pre highBitsK.pub highBits := by
  unfold Impl.MlDsa.AArch64.Round.highBits
  exact zext_ct bits_agree (by taint_decide)

/-- A state satisfying the preconditions of `highBits` and `lowBits`. -/
def bitsSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 261888 | .x2 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩]

theorem highBits_verified : Verified AArch64.target highBits (highBitsContract AArch64.abi) :=
  Verified.of_correct highBits_correct highBits_ct (by
    mldsa_implies [highBitsContract, bitsSig, highBitsK, bitsK, AArch64.abi, AArch64.argRegs] [bitsSat]
      using bitsSat)

/-! ## `lowBits` -/

/-- The constants of `lowBits`. -/
def lbCv (g : Nat) (r : Reg) : BitVec 64 :=
  if r = .x4 then BitVec.ofNat 64 (hbMul g) else if r = .x5 then BitVec.ofNat 64 (hbAdd g)
  else if r = .x7 then BitVec.ofNat 64 (2 * g) else Qv

theorem lbConsts_ok (g : Nat) (hg : IsG g) (s : State) :
    WP isa (.block (lbConsts g)) s fun s' =>
      ((∀ r ∈ [Reg.x4, .x5, .x7, .x9], s'.gpr r = lbCv g r) ∧ s'.mem = s.mem ∧
        (∀ s'', s''.mem = s'.mem → Keep [.x6] s' s'' → True)) ∧ Keep [.x4, .x5, .x7, .x9] s s' := by
  unfold lbConsts
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (hbConsts_ok g hg .x4 .x5 (by decide) s) fun s₁ ⟨⟨h4, h5, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x7 _ s₁) fun s₂ ⟨⟨h7, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (movW_ok .x9 _ s₂) fun s₃ ⟨⟨h9, hm₃⟩, k₃⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm₃, hm₂, hm₁], fun _ _ _ => trivial⟩, ((k₁.trans k₂).trans k₃).mono⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [k₃.get .x4, k₂.get .x4, h4]; rfl
  · rw [k₃.get .x5, k₂.get .x5, h5]; rfl
  · rw [k₃.get .x7, h7]; rcases hg with rfl | rfl <;> decide
  · rw [h9]; exact q32

theorem lowBits_body (s₀ : State) :
    GBody (zextS .x1 s₀) [.x0, .x2] [.x4, .x5, .x7, .x9] [.x2] [.x0, .x2, .x6, .x11, .x12, .x13] .x6 lbCv
      (fun g _ i => (addQ ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64 -
        r1X g ((coeffAt s₀.mem (s₀.gpr .x0) i).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32)
      (fun _ _ _ => True) [.x0] lbBody := by
  intro g _ sL hL hcv hmL he i hi s hI
  have hc : ∀ r ∈ [Reg.x4, .x5, .x7, .x9], s.gpr r = lbCv g r := fun r hr => by
    rw [hI.fixed r hr, hcv r hr]
  refine WP.mono (lbBody_ok g s (hc .x4 (by simp)) (hc .x5 (by simp)) (hc .x7 (by simp)) (hc .x9 (by simp))
    (hI.inR hL (by simp) (by simp) hi) (hI.inW hL (by simp) (by simp) hi))
    fun s' ⟨⟨hm', h0, h2, hc'⟩, hk'⟩ => ⟨⟨?_, fun p hp' => ?_, hc', trivial⟩, hk'⟩
  · rw [hm', hI.read hL (by simp) (by simp) hi, hmL, he .x0 (by simp), zextS_mem, zextS_other s₀ (by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    exacts [h0, h2]

theorem lowBits_correct (s₀ : State) (hp : lowBitsK.pre s₀) :
    ∃ t s', Exec isa lowBits s₀ t s' ∧ abiPreserved s₀ s' ∧ lowBitsK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2.2.2
  obtain ⟨t, s', he, sL, hk, hm, hI⟩ := zext_ok (gamma_ok (gr := .x1) (t := .x3) (ins := [.x0])
    (outs := [.x2]) (fixed := [.x4, .x5, .x7, .x9]) (kc := [.x4, .x5, .x7, .x9]) (bits_g hp) (bits_layout hp)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun g hg s => lbConsts_ok g hg s)
    (lowBits_body s₀))
  have k1 := (zextS_keep .x1 s₀).trans hk
  have e2 : sL.gpr .x2 = s₀.gpr .x2 := k1.get .x2
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, ?_⟩
  refine polyIs_of_toNat fun k hk' => ?_
  rw [← e2, hI.done .x2 (by simp) k hk', zextS_toNat, map_get _ _ hk', lowBits_val hp.2.2.2.1,
    lb_val (isG_of_mem hp.2.2.2.1) (hr k hk'), polyAt_val hr hk']

theorem lowBits_ct : ConstantTime isa lowBitsK.pre lowBitsK.pub lowBits := by
  unfold Impl.MlDsa.AArch64.Round.lowBits
  exact zext_ct bits_agree (by taint_decide)

theorem lowBits_verified : Verified AArch64.target lowBits (lowBitsContract AArch64.abi) :=
  Verified.of_correct lowBits_correct lowBits_ct (by
    mldsa_implies [lowBitsContract, bitsSig, lowBitsK, bitsK, AArch64.abi, AArch64.argRegs] [bitsSat]
      using bitsSat)

end VG.Proof.MlDsa.AArch64.Round
