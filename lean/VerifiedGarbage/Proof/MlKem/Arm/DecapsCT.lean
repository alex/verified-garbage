import VerifiedGarbage.Proof.MlKem.Arm.Decaps
import VerifiedGarbage.Proof.MlKem.Arm.EncryptCT

/-!
# ML-KEM-768 on 32-bit ARM: `vg_mlkem768_decaps`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer, and `ρ` in `dk`, which the contract lets the function leak) leak the
same trace (`all_ct`), phase by phase: the blocks by the taint analysis, from
the pointers, or because they access no memory; the calls of the primitives on
the same pointers; the hashes by `hash_ct`; and the re-encryption by
`encrypt_ct`. The comparison of `c` and `c'` and the selection of the key
branch on nothing but their counters: the taint analysis proves them constant
time from the pointers, which are the same in both runs. What each run is at
each point comes from its correctness (`Decaps.lean`).
-/

namespace VG.Proof.MlKem.Arm.Decaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

theorem ρD_eq (s : State) : ρD s = dkRho mlKem768 (DK s) := by
  show ((((DK s).drop 1152).take 1184).drop 1152).take 32 = ((DK s).drop 2304).take 32
  rw [List.drop_take, List.drop_drop, List.take_take]; rfl

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : Pre s₁
  hp₂ : Pre s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  rho : ρD s₁ = ρD s₂

section
variable {s₁ s₂ : State} (two : Two s₁ s₂)
include two

theorem Two.layEq : lay s₂ = lay s₁ := by
  simp only [Decaps.lay, pScr, pDk, pKey, two.r0, two.r2, two.r3, two.sp]

theorem Two.p0 : (lay s₁).ptr 0 = (lay s₂).ptr 0 := by rw [two.layEq]

/-! ## `û` -/

theorem decU_ct {x y : State} (hx : DD s₁ x) (hy : DD s₂ y) {j : Nat} (hj : j < 3) :
    RelCT isa (fun a b => UInv s₁ x j a ∧ UInv s₂ y j b) decUBody fun a b =>
      (UInv s₁ x (j + 1) a ∧ a.z = decide (j + 1 = 3)) ∧ (UInv s₂ y (j + 1) b ∧ b.z = decide (j + 1 = 3)) := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨decU_step hp₁ hx hj hab.1, decU_step hp₂ hy hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oCin + 320 * j) ∧
        a.gpr .r1 = BitVec.ofNat 32 (32 * 10) ∧ a.gpr .r2 = BitVec.ofNat 32 10 ∧
        a.gpr .r3 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j))) ∧
      (Only w b ∧ b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oCin + 320 * j) ∧
        b.gpr .r1 = BitVec.ofNat 32 (32 * 10) ∧ b.gpr .r2 = BitVec.ofNat 32 10 ∧
        b.gpr .r3 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j))))
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨by rw [hab.1]; exact u1_ok hx hj hu, by rw [hab.2]; exact u1_ok hy hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UB s₁ j u a ∧ UB s₂ j w b)
    (relct_wp (RelCT.callT decompressT (regs4 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1, two.p0],
      by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.p0]⟩))
      fun a b ⟨⟨o₁, a0, a1, a2, a3⟩, ⟨o₂, b0, b1, b2, b3⟩⟩ =>
        ⟨u2_ok hp₁ hx hj hu o₁ a0 a1 a2 a3, u2_ok hp₂ hy hj hw o₂ b0 b1 b2 b3⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (UB s₁ j u a ∧ a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) ∧
        a.gpr .r1 = (lay s₁).ptr 0 + BitVec.ofNat 32 oNtt) ∧
      (UB s₂ j w b ∧ b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) ∧
        b.gpr .r1 = (lay s₂).ptr 0 + BitVec.ofNat 32 oNtt))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨u3_ok hx hj hu hab.1, u3_ok hy hj hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT nttT (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1, two.p0],
      by rw [hab.1.2.2, hab.2.2.2, two.p0]⟩))
    (relct_noMem rfl)

/-! ## K-PKE.Decrypt -/

theorem decrypt_ct {x y : State} (hx : DD s₁ x) (hy : DD s₂ y) :
    RelCT isa (fun a b => a = x ∧ b = y) decrypt fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  -- `û`
  refine RelCT.seq (R := fun (a b : State) => UInv s₁ x 0 a ∧ UInv s₂ y 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact dU_init, by rw [hab.2]; exact dU_init⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UInv s₁ x 3 a ∧ UInv s₂ y 3 b)
    (relct_loop_ne (N := 3) (by decide) fun j hj => decU_ct two hx hy hj) ?_
  refine RelCT.pointwise fun x₃ y₃ ⟨hx₃, hy₃⟩ => ?_
  have d₁ := dU_done hp₁ hx hx₃
  have d₂ := dU_done hp₂ hy hy₃
  obtain ⟨hc₁, g4₁, hs₁, hr₁⟩ := dT_pre hp₁ d₁
  obtain ⟨hc₂, g4₂, hs₂, hr₂⟩ := dT_pre hp₂ d₂
  -- `ŝ`
  refine RelCT.seq (R := fun (a b : State) => DecInv (lay s₁) 2 0 x₃ 0 a ∧ DecInv (lay s₁) 2 0 y₃ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨by rw [hab.1]; exact decT_init, by rw [hab.2]; exact decT_init⟩) ?_
  rw [two.layEq] at hc₂ g4₂ hr₂
  refine RelCT.seq (R := fun (a b : State) => DecInv (lay s₁) 2 0 x₃ 3 a ∧ DecInv (lay s₁) 2 0 y₃ 3 b)
    (relct_loop_ne (N := 3) (by decide) fun j hj => decT_ctG hc₁ hc₂ g4₁ g4₂ hs₁ hr₁ hr₂ hj) ?_
  refine RelCT.pointwise fun x₅ y₅ ⟨hx₅, hy₅⟩ => ?_
  obtain ⟨e₁, ŝ₁, û₁⟩ := dT_done hp₁ d₁ hx₃.u hx₅
  rw [← two.layEq] at hy₅
  obtain ⟨e₂, ŝ₂, û₂⟩ := dT_done hp₂ d₂ hy₃.u hy₅
  -- `ŝ ∘ û`
  refine RelCT.seq (R := fun (a b : State) => DV s₁ (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁)) a ∧
      DV s₂ (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂)) b)
    (relct_wp (dot_ct (L := lay s₁) e₁.env.ctx (by rw [← two.layEq]; exact e₂.env.ctx) ŝ₁ û₁
      (by rw [← two.layEq]; exact ŝ₂) (by rw [← two.layEq]; exact û₂)) fun a b hab =>
      ⟨by rw [hab.1]; exact dDot_ok hp₁ e₁ ŝ₁ û₁, by rw [hab.2]; exact dDot_ok hp₂ e₂ ŝ₂ û₂⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV s₁ (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁)) a ∧ True) ∧
        a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 oAcc ∧ a.gpr .r1 = (lay s₁).ptr 0 + BitVec.ofNat 32 oNtt) ∧
      ((DV s₂ (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂)) b ∧ True) ∧
        b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 oAcc ∧ b.gpr .r1 = (lay s₂).ptr 0 + BitVec.ofNat 32 oNtt))
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1 (by decide) (by decide)) fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩,
        WP.mono (dArgs_ok hp₂ hab.2 (by decide) (by decide)) fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DV s₁ (nttInv (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁))) a ∧
      DV s₂ (nttInv (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂))) b)
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1, two.p0],
      by rw [hab.1.2.2, hab.2.2.2, two.p0]⟩))
      fun a b hab => ⟨dInv_ok hp₁ hab.1.1.1 hab.1.2.1 hab.1.2.2, dInv_ok hp₂ hab.2.1.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `v'`
  refine RelCT.seq (R := fun (a b : State) =>
      (DV s₁ (nttInv (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁))) a ∧
        a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oCin + 960) ∧ a.gpr .r1 = BitVec.ofNat 32 (32 * 4) ∧
        a.gpr .r2 = BitVec.ofNat 32 4 ∧ a.gpr .r3 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oPoly 9)) ∧
      (DV s₂ (nttInv (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂))) b ∧
        b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oCin + 960) ∧ b.gpr .r1 = BitVec.ofNat 32 (32 * 4) ∧
        b.gpr .r2 = BitVec.ofNat 32 4 ∧ b.gpr .r3 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oPoly 9)))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨dV1_ok hp₁ hab.1, dV1_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DV s₁ (nttInv (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁))) a ∧
        PolyIs a.mem ((lay s₁).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₁))) ∧
      (DV s₂ (nttInv (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂))) b ∧
        PolyIs b.mem ((lay s₂).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₂))))
    (relct_wp (RelCT.callT decompressT (regs4 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1, two.p0],
      by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.p0]⟩))
      fun a b ⟨⟨h₁, a0, a1, a2, a3⟩, ⟨h₂, b0, b1, b2, b3⟩⟩ =>
        ⟨dV2_ok hp₁ h₁ a0 a1 a2 a3, dV2_ok hp₂ h₂ b0 b1 b2 b3⟩) ?_
  -- `w`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV s₁ (nttInv (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁))) a ∧
        PolyIs a.mem ((lay s₁).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₁))) ∧
        a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oPoly 9) ∧ a.gpr .r1 = (lay s₁).ptr 0 + BitVec.ofNat 32 oAcc) ∧
      ((DV s₂ (nttInv (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂))) b ∧
        PolyIs b.mem ((lay s₂).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₂))) ∧
        b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oPoly 9) ∧ b.gpr .r1 = (lay s₂).ptr 0 + BitVec.ofNat 32 oAcc))
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1.1 (by decide) (by decide)) fun _ ⟨⟨h, m⟩, g⟩ =>
        ⟨⟨h, by rw [m]; exact hab.1.2⟩, g⟩,
        WP.mono (dArgs_ok hp₂ hab.2.1 (by decide) (by decide)) fun _ ⟨⟨h, m⟩, g⟩ =>
        ⟨⟨h, by rw [m]; exact hab.2.2⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DD s₁ a ∧ PolyIs a.mem ((lay s₁).A 0 (oPoly 9))
        (sub (VG.Proof.MlKem.dcV (CT s₁)) (nttInv (VG.Proof.MlKem.dot3 (sHat s₁) (uHat s₁))))) ∧
      (DD s₂ b ∧ PolyIs b.mem ((lay s₂).A 0 (oPoly 9))
        (sub (VG.Proof.MlKem.dcV (CT s₂)) (nttInv (VG.Proof.MlKem.dot3 (sHat s₂) (uHat s₂))))))
    (relct_wp (RelCT.callT subT (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1, two.p0],
      by rw [hab.1.2.2, hab.2.2.2, two.p0]⟩))
      fun a b hab => ⟨dV4_ok hp₁ hab.1.1.1 hab.1.1.2 hab.1.2.1 hab.1.2.2,
        dV4_ok hp₂ hab.2.1.1 hab.2.1.2 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `m'`
  refine RelCT.seq (R := fun (a b : State) =>
      (a.gpr .r0 = (lay s₁).ptr 0 + BitVec.ofNat 32 (oPoly 9) ∧ a.gpr .r1 = BitVec.ofNat 32 1 ∧
        a.gpr .r2 = (lay s₁).ptr 0 + BitVec.ofNat 32 oMsg ∧ a.gpr .r3 = BitVec.ofNat 32 (32 * 1)) ∧
      (b.gpr .r0 = (lay s₂).ptr 0 + BitVec.ofNat 32 (oPoly 9) ∧ b.gpr .r1 = BitVec.ofNat 32 1 ∧
        b.gpr .r2 = (lay s₂).ptr 0 + BitVec.ofNat 32 oMsg ∧ b.gpr .r3 = BitVec.ofNat 32 (32 * 1)))
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨WP.mono (dM1_ok hp₁ hab.1.1 hab.1.2) fun _ h => h.2, WP.mono (dM1_ok hp₂ hab.2.1 hab.2.2) fun _ h => h.2⟩) ?_
  exact RelCT.callT compressT (regs4 fun a b hab => ⟨by rw [hab.1.1, hab.2.1, two.p0], by rw [hab.1.2.1, hab.2.2.1],
    by rw [hab.1.2.2.1, hab.2.2.2.1, two.p0], by rw [hab.1.2.2.2, hab.2.2.2.2]⟩)


/-! ## The whole function -/

theorem Two.regs {a b : State} (ha : DEnv s₁ a) (hb : DEnv s₂ b) : a.gpr .r7 = b.gpr .r7 := by
  rw [ha.ctx.r7, hb.ctx.r7, two.layEq]

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : DD s₁ a) (hb : DD s₂ b)
    (hi : ∀ {s₀ s : State}, Pre s₀ → DD s₀ s → ∀ p ∈ ins, PieceOk (lay s₀) didx s false p)
    (ho : ∀ {s₀ s : State}, Pre s₀ → DD s₀ s → ∀ p ∈ outs, PieceOk (lay s₀) didx s true p) :
    HashOk (lay s₁) didx ins outs a ∧ HashOk (lay s₁) didx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.env.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩,
    by rw [← two.layEq]; exact ⟨hb.env.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    by rw [ha.env.sp, hb.env.sp, two.sp]⟩

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) decaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hL₁ := lay_ok hp₁
  have hL₂ := lay_ok hp₂
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv s₁ a ∧ a.gpr .r4 = pDk s₁ ∧ a.gpr .r6 = pC s₁ ∧ bytesAt a.mem ((layC s₁).A 2 0) 1088 = CT s₁) ∧
      (DEnv s₂ b ∧ b.gpr .r4 = pDk s₂ ∧ b.gpr .r6 = pC s₂ ∧ bytesAt b.mem ((layC s₂).A 2 0) 1088 = CT s₂))
    (relct_wp (taint_block [.r0, .r1, .r2, .r3] (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact two.r0
        · exact two.r1
        · exact two.r2
        · exact two.r3) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `c` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv s₁ a ∧ a.gpr .r4 = pDk s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oCin) 1088 = CT s₁) ∧
      (DEnv s₂ b ∧ b.gpr .r4 = pDk s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oCin) 1088 = CT s₂))
    (relct_wp (taint_prog [.r6, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.r1
        · exact two.regs hab.1.1 hab.2.1) (by taint_decide))
      fun a b hab =>
        ⟨WP.mono (copyC_ok hp₁ hab.1.1 hab.1.2.2.1 hab.1.2.2.2) fun _ ⟨e, g, c⟩ => ⟨e, by rw [g, hab.1.2.1], c⟩,
          WP.mono (copyC_ok hp₂ hab.2.1 hab.2.2.2.1 hab.2.2.2.2) fun _ ⟨e, g, c⟩ => ⟨e, by rw [g, hab.2.2.1], c⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DD s₁ a ∧ DD s₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨WP.mono ptr6_ok fun _ h => dd_of hp₁ hab.1.1 hab.1.2.1 hab.1.2.2 h,
        WP.mono ptr6_ok fun _ h => dd_of hp₂ hab.2.1 hab.2.2.1 hab.2.2.2 h⟩) ?_
  -- K-PKE.Decrypt
  refine RelCT.seq (R := fun (a b : State) =>
      (DD s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oMsg) 32 = MM s₁) ∧ (DD s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oMsg) 32 = MM s₂))
    (relct_wp (RelCT.pointwise fun x y hxy => decrypt_ct two hxy.1 hxy.2) fun a b hab =>
      ⟨decrypt_ok hp₁ hab.1, decrypt_ok hp₂ hab.2⟩) ?_
  -- `G(m' ‖ h)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oMsg) 32 = MM s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oG) 32 = K1 s₁ ∧
        bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = R1 s₁) ∧
      (DD s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oMsg) 32 = MM s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oG) 32 = K1 s₂ ∧
        bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = R1 s₂))
    (relct_wp (hash_ct (L := lay s₁) (idx := didx) VG.Proof.MlKem.rate72 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r7, oMsg, 32⟩, ⟨.r4, 2336, 32⟩])
        (outs := [⟨.r7, oG, 64⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceD hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact pieceD hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceD hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)))
      fun a b hab =>
        ⟨WP.mono (hashG_ok hp₁ hab.1.1 hab.1.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₁ f (by ddecide) (by decide)).trans hab.1.2, k, r⟩,
         WP.mono (hashG_ok hp₂ hab.2.1 hab.2.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₂ f (by ddecide) (by decide)).trans hab.2.2, k, r⟩⟩) ?_
  -- `J(z ‖ c)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD s₁ a ∧ bytesAt a.mem ((lay s₁).A 0 oMsg) 32 = MM s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oG) 32 = K1 s₁ ∧
        bytesAt a.mem ((lay s₁).A 0 oSigma) 32 = R1 s₁ ∧ bytesAt a.mem ((lay s₁).A 0 oKbar) 32 = KB s₁) ∧
      (DD s₂ b ∧ bytesAt b.mem ((lay s₂).A 0 oMsg) 32 = MM s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oG) 32 = K1 s₂ ∧
        bytesAt b.mem ((lay s₂).A 0 oSigma) 32 = R1 s₂ ∧ bytesAt b.mem ((lay s₂).A 0 oKbar) 32 = KB s₂))
      (relct_wp (hash_ct (L := lay s₁) (idx := didx) VG.Proof.MlKem.rate136 (by decide) (by decide)
        (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r4, 2368, 32⟩, ⟨.r7, oCin, 1088⟩])
          (outs := [⟨.r7, oKbar, 32⟩]) hab.1.1 hab.2.1
          (fun hp h p hp' => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
            rcases hp' with rfl | rfl
            · exact pieceD hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
            · exact pieceD hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide))
          (fun hp h p hp' => by
            rw [List.mem_singleton] at hp'; subst hp'
            exact pieceD hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide)
              (by decide)))
        fun a b hab =>
          ⟨WP.mono (hashJ_ok hp₁ hab.1.1) fun _ ⟨d, f, kb⟩ =>
            ⟨d, (Lay.bytes_keep hL₁ f (by ddecide) (by decide)).trans hab.1.2.1,
              (Lay.bytes_keep hL₁ f (by ddecide) (by decide)).trans hab.1.2.2.1,
              (Lay.bytes_keep hL₁ f (by ddecide) (by decide)).trans hab.1.2.2.2, kb⟩,
           WP.mono (hashJ_ok hp₂ hab.2.1) fun _ ⟨d, f, kb⟩ =>
            ⟨d, (Lay.bytes_keep hL₂ f (by ddecide) (by decide)).trans hab.2.2.1,
              (Lay.bytes_keep hL₂ f (by ddecide) (by decide)).trans hab.2.2.2.1,
              (Lay.bytes_keep hL₂ f (by ddecide) (by decide)).trans hab.2.2.2.2, kb⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DP s₁ a ∧ DP s₂ b)
      (relct_wp (relct_noMem rfl) fun a b ⟨⟨d, m, k, r, kb⟩, ⟨d', m', k', r', kb'⟩⟩ =>
        ⟨ptrs_dp hp₁ d m k r kb, ptrs_dp hp₂ d' m' k' r' kb'⟩) ?_
  -- the re-encryption
  refine RelCT.seq (R := fun (a b : State) => DQ s₁ a ∧ DQ s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab => ⟨reenc_ok hp₁ hab.1, reenc_ok hp₂ hab.2⟩) ?_
  · have ey : EncPre (lay s₁) db y := by rw [← two.layEq]; exact encPre hp₂ hxy.2
    refine encrypt_ct (encPre hp₁ hxy.1) ey ?_
    rw [rhoE_eq hxy.1, two.rho, ← rhoE_eq hxy.2, two.layEq]
  -- the comparison and the selection
  refine RelCT.seq (R := fun (a b : State) => DR s₁ a ∧ DR s₂ b)
    (relct_wp (taint_prog [.r6, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.r6, hab.2.r6, two.layEq]
        · exact two.regs hab.1.env hab.2.env) (by taint_decide))
      fun a b hab => ⟨cmp_ok hp₁ hab.1, cmp_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DS s₁ a ∧ DS s₂ b)
    (relct_wp (taint_block [.r7] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact two.regs hab.1.q.env hab.2.q.env) (by taint_decide))
      fun a b hab => ⟨mask_ok hp₁ hab.1, mask_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DEnv s₁ a ∧ DEnv s₂ b)
    (relct_wp (taint_prog [.r0, .r1, .r2, .r9] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hab.1.r0, hab.2.r0, two.layEq]
        · rw [hab.1.r1, hab.2.r1, two.layEq]
        · rw [hab.1.r2, hab.2.r2]; exact two.r2
        · rw [hab.1.r9, hab.2.r9]) (by taint_decide))
      fun a b hab => ⟨WP.mono (sel_ok hp₁ hab.1) fun _ h => h.1, WP.mono (sel_ok hp₂ hab.2) fun _ h => h.1⟩) ?_
  exact taint_block [.r7] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact two.regs hab.1 hab.2) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.decapsContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem DK_eq (s₀ : State) : DK s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 2400 := by
  simp only [DK, Lay.A, add_ofNat_zero]; rfl

theorem CT_eq (s₀ : State) : CT s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1088 := by
  simp only [CT, Lay.A, add_ofNat_zero]; rfl

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc (ρD s₀) 3 then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = if CT s₀ = C2 s₀ then K1 s₀ else KB s₀) :
    (Spec.MlKem.decapsContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0, ← DK_eq, ← CT_eq]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = if CT s₀ = C2 s₀ then K1 s₀ else KB s₀ := hkey
  rw [e1]
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc (ρD s₀) 3
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.decapsInternal768, VG.Proof.MlKem.kpkeEncrypt768_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.decapsInternal768, VG.Proof.MlKem.kpkeEncrypt768_some (enc_some (r := R1 s₀) hk)]; rfl

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
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.decaps (Spec.MlKem.decapsContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey⟩
  · sig_pub [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρD s₁ = ρD s₂ := by
      rw [ρD_eq, ρD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Decaps
