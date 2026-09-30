import VerifiedGarbage.Proof.MlKem.X86_64.KgX

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen_expanded`, constant time and its contract

Untrusted: everything here is checked by Lean. `vg_mlkem768_keygen`'s
constant time (`KgCT.lean`, `KgTop.lean`, for `kgxK`), and the copies to
`ekx`, which depend only on the pointers; so it leaks only the pointers and
`ρ` (`keyGenX_ct`), and meets the shared contract (`keyGenX_verified`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGenX

open VG.Impl.MlKem.X86_64.KeyGen
open KeyGen (KC KB KFin KRest rhoK R KPre)

theorem copies_tr : RelCT isa (R kgxK fun σ s => KFin σ s ∧ allOk (rhoK σ) 9) copies fun _ _ => True :=
  taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => fa3
    (by rw [h₁.1.kc.top.regs (.r12, .rsi) (by decide), h₂.1.kc.top.regs (.r12, .rsi) (by decide), pub.2.1])
    (by rw [h₁.1.kc.top.regs (.r13, .rdx) (by decide), h₂.1.kc.top.regs (.r13, .rdx) (by decide), pub.2.2.1])
    (by rw [h₁.1.kc.top.regs (.rbx, .rcx) (by decide), h₂.1.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1]))
    (by taint_decide)

theorem body_tr : RelCT isa (R kgxK (KB 9)) (ifOk (.seq rest copies)) (R kgxK KXEnd) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [KeyGen.r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.seq (RelCT.mono KeyGen.rest_tr (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun _ _ h => h) (relInv (fun σ s hp hs => WP.mono (copies_ok hp hs.1) fun _ ⟨hf, hx⟩ =>
        ⟨hf.kc, by rw [hf.r15, ifp hs.2], fun _ => ⟨hf, hx⟩⟩) copies_tr)
    have o₁ := KeyGen.r15_ne h₁.r15 hne
    have o₂ : allOk (rhoK σ₂) 9 := by
      have e : kgRho (KeyGen.kgD σ₁) = kgRho (KeyGen.kgD σ₂) := KeyGen.rho_pub pub
      show allOk (kgRho (KeyGen.kgD σ₂)) 9
      rw [← e]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest.start (h₁.flag (K := kgxK) p₁ (by decide) hx) o₁, o₁⟩,
      ⟨KRest.start (h₂.flag (K := kgxK) p₂ (by decide) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.r15 he
    have o₂ : ¬ allOk (rhoK σ₂) 9 := by
      have e : kgRho (KeyGen.kgD σ₁) = kgRho (KeyGen.kgD σ₂) := KeyGen.rho_pub pub
      show ¬ allOk (kgRho (KeyGen.kgD σ₂)) 9
      rw [← e]; exact o₁
    have k₁ := h₁.flag (K := kgxK) p₁ (by decide) hx
    have k₂ := h₂.flag (K := kgxK) p₂ (by decide) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.r15, fun h => absurd h o₂⟩⟩

end KeyGenX

open KeyGenX in
theorem keyGenX_ct (v : Sample4Impl) :
    ConstantTime isa keyGenXK.pre keyGenXK.pub (Impl.MlKem.X86_64.keyGenX v.callee) := by
  show ConstantTime isa kgxK.pre kgxK.pub _
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem.X86_64.keyGenX
  refine RelCT.seq (relInv (I' := fun σ s => KeyGen.KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) KeyGen.pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KeyGen.KA σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => KeyGen.gRho_ok hp hs.1 hs.2) KeyGen.gRho_tr) ?_
  refine RelCT.seq (RelCT.mono (KeyGen.samples_tr v)
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KeyGen.KB.zero h₁.1 h₁.2,
      KeyGen.KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq body_tr (RelCT.mono KeyGen.epi_tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    ⟨σ₁, σ₂, p₁, p₂, pub, h₁.toKEnd, h₂.toKEnd⟩) fun _ _ _ => trivial)

/-- A state satisfying `keyGenExpandedContract`'s precondition. -/
def keyGenXSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x6000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 10432⟩, ⟨0x6000, 2400⟩, ⟨0x10000, 32768⟩]

theorem keyGenX_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.keyGenX v.callee) (Spec.MlKem.keyGenExpandedContract X86_64.abi 32) :=
  Verified.of_correct (keyGenX_correct v) (keyGenX_ct v)
    { pre := by
        intro s h
        sig_pre [Spec.MlKem.keyGenExpandedContract, Spec.MlKem.keyGenExpandedSig, X86_64.abi, VG.X86_64.argRegs]
          at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.keyGenExpandedContract, Spec.MlKem.keyGenExpandedSig, keyGenXK, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.keyGenExpandedContract, Spec.MlKem.keyGenExpandedSig, keyGenXK, X86_64.abi,
          VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.keyGenExpandedContract, Spec.MlKem.keyGenExpandedSig, keyGenXK,
        X86_64.abi, VG.X86_64.argRegs] [keyGenXSat] using keyGenXSat }

end VG.Proof.MlKem.X86_64
