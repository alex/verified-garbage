import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Scalar

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4` and `vg_mldsa_expand_mask_poly4_avx2`, verified

Untrusted: everything here is checked by Lean. The baseline implementation
is constant time as the calls are (`expandMask_ct`, from their pointers and
`γ₁`), and the contract of the proofs (`em4K`) is the shared one of `Spec/`.
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R fun σ s => ArgI σ K s) (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask)
      (R fun σ s => PC σ (K + 1) s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK h) (RelCT.callEx expandMask_correct expandMask_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, hq.2.2.2.2]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [emK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi,
        h₁.rdx, h₂.rdx, h₁.rcx, h₂.rcx]
      simp only [sd, aP, at', scr, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
        .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
        .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R fun σ s => PC σ K s) (callK K) (R fun σ s => PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, sd, sd, hq.1]
        · exact env_r13 hq h₁.env h₂.env
        · exact env_rbx hq h₁.env h₂.env) c))
    (call_ct hK)

theorem ct_scalar : ConstantTime isa em4K.pre em4K.pub expandMask4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (pre_of hp)) fun _ h => ⟨h, fun _ h => absurd h (by omega)⟩)
    (taintRel [.rdi, .rdx, .rcx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

/-- A state satisfying the precondition. -/
def em4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 264⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem em4_verified (c : Prog isa)
    (hc : ∀ σ, em4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s')
    (ht : ConstantTime isa em4K.pre em4K.pub c) :
    Verified X86_64.target c (Spec.MlDsa.expandMask4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := by sig_implies_pre [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, em4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, em4K, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, em4K, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Spec.MlDsa.expandMask4Contract, Spec.MlDsa.expandMask4Sig, em4K, X86_64.abi,
        X86_64.argRegs] [em4Sat] using em4Sat }

theorem expandMask4Avx2_verified : Verified X86_64.target expandMask4Avx2
    (Spec.MlDsa.expandMask4Contract X86_64.abi 24) := em4_verified _ correct ct

theorem expandMask4_verified : Verified X86_64.target expandMask4
    (Spec.MlDsa.expandMask4Contract X86_64.abi 24) := em4_verified _ correct_scalar ct_scalar

end VG.Proof.MlDsa.X86_64.Mask4
