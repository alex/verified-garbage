import VerifiedGarbage.Proof.MlKem.Arm.Encaps
import VerifiedGarbage.Proof.MlKem.Arm.EncryptCT

/-!
# ML-KEM on 32-bit ARM: encapsulation, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer, `scratch` on the stack, and `ρ` of `ek`, which the contract lets the
function leak) leak the same trace (`all_ct`), phase by phase: the load of
`scratch` from the stack pointer; the blocks by the taint analysis, from the
pointers, or because they access no memory; the hashes by `hash_ct`; and
K-PKE.Encrypt by `encrypt_ct`, whose `SampleNTT`s take the seeds of the same
`ρ`. What each run is at each point comes from its correctness
(`Encaps.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation. Its `outcome` is the contract's, which ML-KEM-768's
`verified` (below) and ML-KEM-1024's (`Proof/MlKem1024/Arm/`) use.
-/

namespace VG.Proof.MlKem.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-- A load from the stack leaks its address, the same in two runs with the
same stack pointer. -/
theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  scr : stackArg s₁ 0 = stackArg s₂ 0
  rho : ekRho K.p (EK K s₁) = ekRho K.p (EK K s₂)

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.r0, two.r2, two.r3, two.sp, two.scr]

theorem Two.regs {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) :
    ∀ r ∈ [Reg.r4, .r6, .r7, .r8], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r4, hb.r4]; exact two.r0
  · rw [ha.r6, hb.r6]; exact two.r2
  · rw [ha.ctx.r7, hb.ctx.r7, two.layEq]
  · rw [ha.r8, hb.r8]; exact two.r3

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.r4, .r6, .r7, .r8] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) eidx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) eidx s true p) :
    HashOk (lay s₁ K) eidx ins outs a ∧ HashOk (lay s₁ K) eidx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩, by rw [← two.layEq]; exact ⟨hb.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    by rw [ha.sp, hb.sp, two.sp]⟩

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
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
      (EnEnv K s₁ a ∧ a.gpr .r5 = pM s₁ ∧ bytesAt a.mem ((layM s₁ K).A 2 0) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ b.gpr .r5 = pM s₂ ∧ bytesAt b.mem ((layM s₂ K).A 2 0) 32 = M K s₂))
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
      (EnEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = M K s₂))
    (relct_wp (taint_prog [.r5, .r7] (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r1
        · exact two.regs hab.1.1 hab.2.1 .r7 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyM_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, copyM_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => F4 K s₁ a ∧ F4 K s₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨s4_ok hp₁ hab.1.1 hab.1.2, s4_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `H(ek)`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate136 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r4, 0, K.ekLen⟩]) (outs := [⟨.r7, oHek, 32⟩])
        hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) enc0 hK.encEk (by dsimp only; offs) (by dsimp only; offs) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)))
      fun a b hab => ⟨s5_ok hp₁ hab.1, s5_ok hp₂ hab.2⟩) ?_
  -- `G(m ‖ H(ek))`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = KK K s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = KK K s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate72 (by decide) (by decide)
      (List.cons_ne_nil _ _) fun a b hab => two.hashOk (ins := [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩])
        (outs := [⟨.r7, oG, 64⟩]) hab.1.1.1 hab.2.1.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)
          · exact pieceE hp h (.inr rfl) (by simp) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by edecide) (by edecide) (by edecide) (by edecide) (by edecide)))
      fun a b hab => ⟨s6_ok hp₁ hab.1, s6_ok hp₂ hab.2⟩) ?_
  -- `K` into `key`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 3 0) 32 = KK K s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 3 0) 32 = KK K s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (taint_prog [.r6, .r7] (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt
  refine RelCT.seq (R := fun (a b : State) => EnEnv K s₁ a ∧ EnEnv K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.r7] (fun a b hab => two.sub' hab.1 hab.2) (by taint_decide))
  have ey : EncPre K (lay s₁ K) eb y := by rw [← two.layEq]; exact encPre hp₂ hxy.2.1.1 hxy.2.1.2.1
  refine encrypt_ct (encPre hp₁ hxy.1.1.1 hxy.1.1.2.1) ey ?_
  show ekRho K.p (bytesAt x.mem ((lay s₁ K).A 2 0) K.ekLen) = ekRho K.p (bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen)
  have e₂ : bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen = EK K s₂ := by rw [← two.layEq]; exact hxy.2.1.1.ek
  rw [hxy.1.1.1.ek, e₂]; exact two.rho

end

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => encapsInternal K.p iters (EK K s₀) (M K s₀))
      (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0)
      (KK K s₀, VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ekRho K.p (EK K s₀)) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := RR K s₀) hk)]; rfl

theorem EK_eq (K : KemLay) (s₀ : State) : EK K s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) K.ekLen := by
  simp only [EK, Lay.A, add_ofNat_zero]; rfl

theorem M_eq (K : KemLay) (s₀ : State) : M K s₀ = bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 32 := by
  simp only [M, Lay.A, add_ofNat_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Spec.MlKem.encapsContract Arm.abi 8).pre s) : Pre kl768 s := by
  sig_pre [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3, b4, b5, b6,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨kl768_wf, kl768_calls, h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3,
    b4, b5, b6, f1, f2, f3, f4, f5⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = KK kl768 s₀)
    (hct : bytesAt s.mem (State.addr (pCt s₀)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀)) :
    (Spec.MlKem.encapsContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1184 = EK kl768 s₀ := (EK_eq kl768 s₀).symm
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = KK kl768 s₀ := hkey
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀) := hct
  rw [e0, ← M_eq, e1, e2]
  exact outcome kl768_wf s₀

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
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.encaps (Spec.MlKem.encapsContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey hct⟩
  · sig_pub [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, hs⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 s₁) = ekRho kl768.p (EK kl768 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hs, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Encaps
