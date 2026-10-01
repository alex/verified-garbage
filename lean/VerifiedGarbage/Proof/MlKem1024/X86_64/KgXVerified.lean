import VerifiedGarbage.Proof.MlKem1024.X86_64.KgX

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen_expanded`, constant time and its contract

Untrusted: everything here is checked by Lean. `vg_mlkem1024_keygen`'s
constant time (`KgCT.lean`, `KgTop.lean`, for `kgxK`), and the copies to
`ekx`, which depend only on the pointers; so it leaks only the pointers and
`ρ` (`keyGenX1024_ct`), and meets the shared contract (`keyGenX1024_verified`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGenX4

open VG.Impl.MlKem1024.X86_64.KeyGen1024
open KeyGen4 (KC KB KFin KRest rhoK R KPre)

theorem copies_tr : RelCT isa (R kgxK fun σ s => KFin σ s ∧ allOk4 (rhoK σ) 16) copies fun _ _ => True :=
  taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => fa3
    (by rw [h₁.1.kc.top.regs (.r12, .rsi) (by decide), h₂.1.kc.top.regs (.r12, .rsi) (by decide), pub.2.1])
    (by rw [h₁.1.kc.top.regs (.r13, .rdx) (by decide), h₂.1.kc.top.regs (.r13, .rdx) (by decide), pub.2.2.1])
    (by rw [h₁.1.kc.top.regs (.rbx, .rcx) (by decide), h₂.1.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1]))
    (by taint_decide)

theorem body_tr : RelCT isa (R kgxK (KB 16)) (ifOk (.seq rest copies)) (R kgxK KXEnd) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [KeyGen4.r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.seq (RelCT.mono KeyGen4.rest_tr (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun _ _ h => h) (relInv (fun σ s hp hs => WP.mono (copies_ok hp hs.1) fun _ ⟨hf, hx⟩ =>
        ⟨hf.kc, by rw [hf.r15, ifp hs.2], fun _ => ⟨hf, hx⟩⟩) copies_tr)
    have o₁ := KeyGen4.r15_ne h₁.r15 hne
    have o₂ : allOk4 (rhoK σ₂) 16 := by
      have e : kgRho1024 (KeyGen4.kgD σ₁) = kgRho1024 (KeyGen4.kgD σ₂) := KeyGen4.rho_pub pub
      show allOk4 (kgRho1024 (KeyGen4.kgD σ₂)) 16
      rw [← e]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest.start (h₁.flag (K := kgxK) p₁ (by decide) hx) o₁, o₁⟩,
      ⟨KRest.start (h₂.flag (K := kgxK) p₂ (by decide) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := KeyGen4.r15_eq h₁.r15 he
    have o₂ : ¬ allOk4 (rhoK σ₂) 16 := by
      have e : kgRho1024 (KeyGen4.kgD σ₁) = kgRho1024 (KeyGen4.kgD σ₂) := KeyGen4.rho_pub pub
      show ¬ allOk4 (kgRho1024 (KeyGen4.kgD σ₂)) 16
      rw [← e]; exact o₁
    have k₁ := h₁.flag (K := kgxK) p₁ (by decide) hx
    have k₂ := h₂.flag (K := kgxK) p₂ (by decide) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.r15, fun h => absurd h o₂⟩⟩

end KeyGenX4

open KeyGenX4 in
theorem keyGenX1024_ct (v : Sample4Impl) :
    ConstantTime isa keyGenX1024K.pre keyGenX1024K.pub (Impl.MlKem1024.X86_64.keyGenX1024 v.callee) := by
  show ConstantTime isa kgxK.pre kgxK.pub _
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem1024.X86_64.keyGenX1024
  refine RelCT.seq (relInv (I' := fun σ s => KeyGen4.KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) KeyGen4.pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KeyGen4.KA σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => KeyGen4.gRho_ok hp hs.1 hs.2) KeyGen4.gRho_tr) ?_
  refine RelCT.seq (RelCT.mono (KeyGen4.samples_tr v)
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KeyGen4.KB.zero h₁.1 h₁.2,
      KeyGen4.KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq body_tr (RelCT.mono KeyGen4.epi_tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    ⟨σ₁, σ₂, p₁, p₂, pub, h₁.toKEnd, h₂.toKEnd⟩) fun _ _ _ => trivial)

/-- A state satisfying `keyGenExpandedContract`'s precondition. -/
def keyGenX1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x7000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 17984⟩, ⟨0x7000, 3168⟩, ⟨0x10000, 49152⟩]

theorem keyGenX1024_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem1024.X86_64.keyGenX1024 v.callee) (Spec.MlKem1024.keyGenExpandedContract X86_64.abi 32) :=
  Verified.of_correct (keyGenX1024_correct v) (keyGenX1024_ct v)
    { pre := by
        intro s h
        sig_pre [Spec.MlKem1024.keyGenExpandedContract, Spec.MlKem1024.keyGenExpandedSig, X86_64.abi, VG.X86_64.argRegs]
          at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem1024.keyGenExpandedContract, Spec.MlKem1024.keyGenExpandedSig, keyGenX1024K, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.keyGenExpandedContract, Spec.MlKem1024.keyGenExpandedSig, keyGenX1024K, X86_64.abi,
          VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.keyGenExpandedContract, Spec.MlKem1024.keyGenExpandedSig, keyGenX1024K,
        X86_64.abi, VG.X86_64.argRegs] [keyGenX1024Sat] using keyGenX1024Sat }

end VG.Proof.MlKem1024.X86_64
