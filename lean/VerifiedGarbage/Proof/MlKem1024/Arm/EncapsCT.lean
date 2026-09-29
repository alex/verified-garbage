import VerifiedGarbage.Proof.MlKem1024.Arm.Encaps
import VerifiedGarbage.Proof.MlKem1024.Arm.EncryptCT
import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_encaps`, constant time and `Verified`

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public data (the pointers, the stack pointer, `scratch` on the
stack, and `ρ` of `ek`, which the contract lets the function leak) leak the
same trace (`all_ct`), phase by phase: the load of `scratch` from the stack
pointer; the blocks by the taint analysis, from the pointers, or because
they access no memory; the hashes by `hash_ct`; and K-PKE.Encrypt by
`encrypt_ct`, whose `SampleNTT`s take the seeds of the same `ρ`. What each
run is at each point comes from its correctness (`Encaps.lean`).
-/

namespace VG.Proof.MlKem1024.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc (EB)
open VG.Proof.MlKem1024.Arm.Enc
open VG.Proof.MlKem.Arm.Encaps (relct_ldrSp)
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
  scr : stackArg s₁ 0 = stackArg s₂ 0
  rho : ekRho mlKem1024 (EK s₁) = ekRho mlKem1024 (EK s₂)

section
variable {s₁ s₂ : State} (two : Two s₁ s₂)
include two

theorem Two.layEq : lay s₂ = lay s₁ := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.r0, two.r2, two.r3, two.sp, two.scr]

theorem Two.regs {a b : State} (ha : EnEnv s₁ a) (hb : EnEnv s₂ b) :
    ∀ r ∈ [Reg.r4, .r6, .r7, .r8], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r4, hb.r4]; exact two.r0
  · rw [ha.r6, hb.r6]; exact two.r2
  · rw [ha.ctx.r7, hb.ctx.r7, two.layEq]
  · rw [ha.r8, hb.r8]; exact two.r3

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv s₁ a) (hb : EnEnv s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.r4, .r6, .r7, .r8] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : EnEnv s₁ a) (hb : EnEnv s₂ b)
    (hi : ∀ {s₀ s : State}, Pre s₀ → EnEnv s₀ s → ∀ p ∈ ins, PieceOk (lay s₀) eidx s false p)
    (ho : ∀ {s₀ s : State}, Pre s₀ → EnEnv s₀ s → ∀ p ∈ outs, PieceOk (lay s₀) eidx s true p) :
    HashOk (lay s₁) eidx ins outs a ∧ HashOk (lay s₁) eidx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩, by rw [← two.layEq]; exact ⟨hb.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    by rw [ha.sp, hb.sp, two.sp]⟩

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) encaps1024 fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  -- `scratch` from the stack
  refine RelCT.seq (R := fun (a b : State) =>
      (a.gpr .r12 = pScr s₁ ∧ (∀ r, r ≠ .r12 → a.gpr r = s₁.gpr r) ∧ a.mem = s₁.mem ∧ a.rd = s₁.rd ∧
        a.wr = s₁.wr ∧ a.sp = s₁.sp) ∧
      (b.gpr .r12 = pScr s₂ ∧ (∀ r, r ≠ .r12 → b.gpr r = s₂.gpr r) ∧ b.mem = s₂.mem ∧ b.rd = s₂.rd ∧
        b.wr = s₂.wr ∧ b.sp = s₂.sp))
    (relct_wp (relct_ldrSp fun a b hab => by rw [hab.1, hab.2, two.sp]) fun a b hab =>
      ⟨by rw [hab.1]; exact ldrSp_ok hp₁, by rw [hab.2]; exact ldrSp_ok hp₂⟩) ?_
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv s₁ a ∧ a.gpr .r5 = pM s₁ ∧ bytesAt a.mem ((layM s₁).A 2 0) 32 = M s₁) ∧
      (EnEnv s₂ b ∧ b.gpr .r5 = pM s₂ ∧ bytesAt b.mem ((layM s₂).A 2 0) 32 = M s₂))
    (relct_wp (taint_block [.r0, .r1, .r2, .r3, .r12] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨⟨a12, ar, -⟩, ⟨b12, br, -⟩⟩ := hab
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r0
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r1
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r2
        · rw [ar _ (by decide), br _ (by decide)]; exact two.r3
        · rw [a12, b12]; exact two.scr) (by taint_decide))
      fun a b ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩⟩ =>
        ⟨setup_ok hp₁ a1 a2 a3 a4 a5 a6, setup_ok hp₂ b1 b2 b3 b4 b5 b6⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oMsg) 32 = M s₁) ∧
      (EnEnv s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oMsg) 32 = M s₂))
    (relct_wp (taint_prog [.r5, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r1
        · exact two.regs hab.1.1 hab.2.1 .r7 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyM_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, copyM_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => F4 s₁ a ∧ F4 s₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨s4_ok hp₁ hab.1.1 hab.1.2, s4_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `H(ek)`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oHek) 32 = H (EK s₁)) ∧
      (F4 s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oHek) 32 = H (EK s₂)))
    (relct_wp (hash_ct (L := lay s₁) (idx := eidx) VG.Proof.MlKem.rate136 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r4, 0, 1568⟩]) (outs := [⟨.r7, oHek, 32⟩])
        hab.1.1 hab.2.1
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)))
      fun a b hab => ⟨s5_ok hp₁ hab.1, s5_ok hp₂ hab.2⟩) ?_
  -- `G(m ‖ H(ek))`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oG) 32 = KK s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = RR s₁) ∧
      (F4 s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oG) 32 = KK s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = RR s₂))
    (relct_wp (hash_ct (L := lay s₁) (idx := eidx) VG.Proof.MlKem.rate72 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩])
        (outs := [⟨.r7, oG, 64⟩]) hab.1.1.1 hab.2.1.1
        (fun hp h p hp' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)))
      fun a b hab => ⟨s6_ok hp₁ hab.1, s6_ok hp₂ hab.2⟩) ?_
  -- `K` into `key`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 s₁ a ∧ bytesAt a.mem ((lay s₁).A 3 0) 32 = KK s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = RR s₁) ∧
      (F4 s₂ b ∧ bytesAt b.mem ((lay s₂).A 3 0) 32 = KK s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = RR s₂))
    (relct_wp (taint_prog [.r6, .r7] (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt
  refine RelCT.seq (R := fun (a b : State) => EnEnv s₁ a ∧ EnEnv s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.r7] (fun a b hab => two.sub' hab.1 hab.2) (by taint_decide))
  have ey : EncPre (lay s₁) eb y := by rw [← two.layEq]; exact encPre hp₂ hxy.2.1.1 hxy.2.1.2.1
  refine encrypt_ct (encPre hp₁ hxy.1.1.1 hxy.1.1.2.1) ey ?_
  show ekRho mlKem1024 (bytesAt x.mem ((lay s₁).A 2 0) 1568) = ekRho mlKem1024 (bytesAt y.mem ((lay s₁).A 2 0) 1568)
  have e₂ : bytesAt y.mem ((lay s₁).A 2 0) 1568 = EK s₂ := by rw [← two.layEq]; exact hxy.2.1.1.ek
  rw [hxy.1.1.1.ek, e₂]; exact two.rho

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem1024.encapsContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3, b4, b5, b6,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3, b4, b5, b6,
    f1, f2, f3, f4, f5⟩

theorem EK_eq (s₀ : State) : EK s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1568 := by
  simp only [EK, Lay.A, add_ofNat_zero]; rfl

theorem M_eq (s₀ : State) : M s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 32 := by
  simp only [M, Lay.A, add_ofNat_zero]; rfl

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc (ekRho mlKem1024 (EK s₀)) 4 then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = KK s₀)
    (hct : bytesAt s.mem (State.addr (pCt s₀)) 1568 =
      VG.Proof.MlKem.ct1024 (aEnc (ekRho mlKem1024 (EK s₀)) (RR s₀)) (EK s₀) (M s₀) (RR s₀)) :
    (Spec.MlKem1024.encapsContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0, ← EK_eq, ← M_eq]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = KK s₀ := hkey
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 1568 =
      VG.Proof.MlKem.ct1024 (aEnc (ekRho mlKem1024 (EK s₀)) (RR s₀)) (EK s₀) (M s₀) (RR s₀) := hct
  rw [e1, e2]
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc (ekRho mlKem1024 (EK s₀)) 4
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.encapsInternal1024, VG.Proof.MlKem.kpkeEncrypt1024_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.encapsInternal1024, VG.Proof.MlKem.kpkeEncrypt1024_some (enc_some (r := RR s₀) hk)]; rfl

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0 else if a = 0x8001 then 0 else if a = 0x8002 then 1 else 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified : Verified Arm.target Impl.MlKem1024.Arm.encaps1024 (Spec.MlKem1024.encapsContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey hct⟩
  · sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, hs⟩ := hpub
    have hr : ekRho mlKem1024 (EK s₁) = ekRho mlKem1024 (EK s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hs, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    have ea : stackArgAddr satState 0 = 0x8000 := by decide
    have eb : stackArg satState 0 = 0x10000 := by decide
    rw [ea, eb]
    exact ⟨by decide, by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide⟩

end VG.Proof.MlKem1024.Arm.Encaps
