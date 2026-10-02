import VerifiedGarbage.Proof.MlKem.Arm.KeyGen
import VerifiedGarbage.Proof.MlKem.Arm.RowCT

/-!
# ML-KEM-768 on 32-bit ARM: `vg_mlkem768_keygen`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer and `ρ`, which the contract lets the function leak) leak the same
trace (`all_ct`), phase by phase: the blocks by the taint analysis, from the
pointers, or because they access no memory (`relct_noMem`); the hashes by
`hash_ct`; the `PRF`s by `prfLoop_ct`; the rows of `t̂` by `rowSum_ct`, whose
`SampleNTT`s take the same seeds `ρ ‖ j ‖ i` in both runs; and the calls of
the primitives on the same pointers (`RelCT.callT`). What each run is at each
point comes from its correctness (`KeyGen.lean`).
-/

namespace VG.Proof.MlKem.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : Pre s₁
  hp₂ : Pre s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  rho : ρ₀ s₁ = ρ₀ s₂

section
variable {s₁ s₂ : State} (two : Two s₁ s₂)
include two

theorem Two.lay : lay s₂ = lay s₁ := by
  simp only [KeyGen.lay, pSeed, pEk, pDk, pScr, two.r0, two.r1, two.r2, two.r3, two.sp]

/-- The registers that hold pointers are the same in both runs. -/
theorem Two.regs {a b : State} (ha : KEnv s₁ a) (hb : KEnv s₂ b) :
    ∀ r ∈ [Reg.r4, .r5, .r6, .r7], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r4, hb.r4]; exact two.r0
  · rw [ha.r5, hb.r5]; exact two.r1
  · rw [ha.r6, hb.r6]; exact two.r2
  · rw [ha.ctx.r7, hb.ctx.r7, two.lay]

theorem Two.sub {rs : List Reg} (hs : ∀ r ∈ rs, r ∈ [Reg.r4, .r5, .r6, .r7]) {a b : State} (ha : KEnv s₁ a)
    (hb : KEnv s₂ b) : ∀ r ∈ rs, a.gpr r = b.gpr r := fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : KEnv s₁ a) (hb : KEnv s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

/-! ## The rows of `t̂` -/

theorem kgRow_ct {i : Nat} (hi : i < 3) :
    RelCT isa (fun a b => KRow s₁ i a ∧ KRow s₂ i b) kgRowBody fun a b =>
      (KRow s₁ (i + 1) a ∧ a.z = decide (i + 1 = 3)) ∧ (KRow s₂ (i + 1) b ∧ b.z = decide (i + 1 = 3)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have py : RowPre (lay s₁) (ρ₀ s₁) (VG.Proof.MlKem.kgS (D s₂)) i (okK s₂ i) y := by
    have := hy.rowPre hi; rwa [two.lay, ← two.rho] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b : State) =>
      RowInv (lay s₁) false (ρ₀ s₁) (VG.Proof.MlKem.kgS (D s₁)) i (okK s₁ i) x 3 a ∧
      RowInv (lay s₂) false (ρ₀ s₂) (VG.Proof.MlKem.kgS (D s₂)) i (okK s₂ i) y 3 b)
    (relct_wp (rowSum_ct (hx.rowPre hi) py) fun a b hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hx.rowPre hi), by rw [hab.2]; exact rowSum_ok (hy.rowPre hi)⟩) ?_
  -- `t̂[i] += ê[i]`
  refine RelCT.seq (R := fun (a b : State) => KR2 s₁ i x a ∧ KR2 s₂ i y b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨kr2_ok hi hx hab.1, kr2_ok hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR3 s₁ i x a ∧ KR3 s₂ i y b)
    (relct_wp (RelCT.callT addT (regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨kr3_ok hp₁ hi hx hab.1, kr3_ok hp₂ hi hy hab.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b : State) => KR4 s₁ i x a ∧ KR4 s₂ i y b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨kr4_ok hi hx hab.1, kr4_ok hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR5 s₁ i x a ∧ KR5 s₂ i y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨kr5_ok hp₁ hi hx hab.1, kr5_ok hp₂ hi hy hab.2⟩) ?_
  exact relct_wp (relct_noMem rfl) fun a b hab => ⟨kr6_ok hp₁ hi hx hab.1, kr6_ok hp₂ hi hy hab.2⟩

/-! ## `ŝ` into `dk` -/

theorem kgS_ct {j : Nat} (hj : j < 3) :
    RelCT isa (fun a b => KS s₁ j a ∧ KS s₂ j b) kgSBody fun a b =>
      (KS s₁ (j + 1) a ∧ a.z = decide (j + 1 = 3)) ∧ (KS s₂ (j + 1) b ∧ b.z = decide (j + 1 = 3)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine RelCT.seq (R := fun (a b : State) => KS1 s₁ j x a ∧ KS1 s₂ j y b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact ks1_ok hj hx,
      by rw [hab.2]; exact ks1_ok hj hy⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KS2 s₁ j x a ∧ KS2 s₂ j y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.r0, hab.2.r0, two.lay], by rw [hab.1.r1, hab.2.r1, two.lay]⟩))
      fun a b hab => ⟨ks2_ok hp₁ hj hx hab.1, ks2_ok hp₂ hj hy hab.2⟩) ?_
  exact relct_wp (relct_noMem rfl) fun a b hab => ⟨ks3_ok hp₁ hj hx hab.1, ks3_ok hp₂ hj hy hab.2⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) keygen fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  -- the setup
  refine RelCT.seq (R := fun (a b : State) => (KEnv s₁ a ∧ a.mem ((lay s₁).A 0 oK) = 3) ∧
      (KEnv s₂ b ∧ b.mem ((lay s₂).A 0 oK) = 3))
    (relct_wp (taint_block [.r0, .r1, .r2, .r3] (fun a b hab r hr => by
      rw [hab.1, hab.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact two.r0
      · exact two.r1
      · exact two.r2
      · exact two.r3) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `G(d ‖ 3)`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oG) 32 = VG.Proof.MlKem.kgRho (D s₁) ∧
        bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma (D s₁)) ∧
      (KEnv s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oG) 32 = VG.Proof.MlKem.kgRho (D s₂) ∧
        bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma (D s₂)))
    (relct_wp (hash_ct (L := lay s₁) (idx := kidx) rate72 (by decide) (by decide) (List.cons_ne_nil _ _)
      fun a b hab => ⟨⟨hab.1.1.ctx, g_ins hp₁ hab.1.1, g_outs hp₁ hab.1.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.1.ctx, g_ins hp₂ hab.2.1, g_outs hp₂ hab.2.1⟩,
        two.spE hab.1.1 hab.2.1⟩)
      fun a b hab => ⟨g_ok hp₁ hab.1.1 hab.1.2, g_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `ρ`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho (D s₁) ∧
        bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma (D s₁)) ∧
      (KEnv s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho (D s₂) ∧
        bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma (D s₂)))
    (relct_wp (taint_prog [.r7] (fun a b hab => two.sub (by simp) hab.1.1 hab.2.1) (by taint_decide))
      fun a b hab => ⟨rho_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, rho_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the `PRF`s
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho (D s₁) ∧
        ∀ N < 6, PolyIs a.mem ((lay s₁).A 0 (oPoly (3 + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma (D s₁)) N))) ∧
      (KEnv s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho (D s₂) ∧
        ∀ N < 6, PolyIs b.mem ((lay s₂).A 0 (oPoly (3 + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma (D s₂)) N))))
    (relct_wp (RelCT.pointwise fun x y hxy =>
      prfLoop_ct (L := lay s₁) true (by decide) (by decide) hxy.1.1.ctx
        (by rw [← two.lay]; exact hxy.2.1.ctx) rfl rfl)
      fun a b hab => ⟨prf_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, prf_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the rows of `t̂`
  refine RelCT.seq (R := fun (a b : State) => KRow s₁ 0 a ∧ KRow s₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨rows_init hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, rows_init hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KRow s₁ 3 a ∧ KRow s₂ 3 b)
    (relct_loop_ne (N := 3) (by decide) fun i hi => kgRow_ct two hi) ?_
  -- `ŝ` into `dk`
  refine RelCT.seq (R := fun (a b : State) => KS s₁ 0 a ∧ KS s₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨s_init hp₁ hab.1, s_init hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv s₁ a ∧ KEnv s₂ b)
    (RelCT.mono (relct_loop_ne (N := 3) (by decide) fun j hj => kgS_ct two hj) (fun _ _ h => h)
      fun _ _ h => ⟨h.1.env, h.2.env⟩) ?_
  -- the end
  refine RelCT.seq (R := fun (a b : State) => KEnv s₁ a ∧ KEnv s₂ b)
    (relct_wp (taint_prog [.r5, .r7] (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide))
      fun a b hab => ⟨cpRho_env hp₁ hab.1, cpRho_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv s₁ a ∧ KEnv s₂ b)
    (relct_wp (taint_prog [.r5, .r6] (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide))
      fun a b hab => ⟨cpEk_env hp₁ hab.1, cpEk_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv s₁ a ∧ KEnv s₂ b)
    (relct_wp (hash_ct (L := lay s₁) (idx := kidx) rate136 (by decide) (by decide) (List.cons_ne_nil _ _)
      fun a b hab => ⟨⟨hab.1.ctx, h_ins hp₁ hab.1, h_outs hp₁ hab.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.ctx, h_ins hp₂ hab.2, h_outs hp₂ hab.2⟩, two.spE hab.1 hab.2⟩)
      fun a b hab => ⟨hashH_env hp₁ hab.1, hashH_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv s₁ a ∧ KEnv s₂ b)
    (relct_wp (taint_prog [.r4, .r6] (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide))
      fun a b hab => ⟨cpZ_env hp₁ hab.1, cpZ_env hp₂ hab.2⟩) ?_
  exact taint_block [.r7] (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.keyGenContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem sample_some {s₀ : State} (hk : okK s₀ 3 = true) :
    ∀ i < 3, ∀ j < 3, sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.kgRho (D s₀)) i j) = some (aK s₀ i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk i (List.mem_range.mpr hi)
  have h₂ := List.all_eq_true.mp h₁ j (List.mem_range.mpr hj)
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aK, effA, rowSeed, Bool.false_eq_true, ite_false, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem sample_none {s₀ : State} (hk : okK s₀ 3 = false) :
    ∃ i < 3, ∃ j < 3, sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.kgRho (D s₀)) i j) = none := by
  rw [okK, List.all_eq_false] at hk
  obtain ⟨i, hi, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨j, hj, h₂⟩ := h₁
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okK s₀ 3 then 1 else 0)
    (hek : bytesAt s.mem (State.addr (pEk s₀)) 1184 = EK s₀) (hdk : bytesAt s.mem (State.addr (pDk s₀)) 2400 = DK s₀) :
    (Spec.MlKem.keyGenContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1184 = EK s₀ := hek
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 2400 = DK s₀ := hdk
  have eD : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 32 = D s₀ := rfl
  have eZ : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0) + 32) 32 = Z s₀ := rfl
  rw [e1, e2, eD, eZ]
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okK s₀ 3
  · obtain ⟨i, hi, j, hj, hn⟩ := sample_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.keyGenInternal768, VG.Proof.MlKem.kpkeKeyGen768_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.keyGenInternal768, VG.Proof.MlKem.kpkeKeyGen768_some (sample_some hk)]; rfl

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.keygen (Spec.MlKem.keyGenContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hek hdk⟩
  · sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρ₀ s₁ = ρ₀ s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.KeyGen
