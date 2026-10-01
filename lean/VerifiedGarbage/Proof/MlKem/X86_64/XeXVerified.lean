import VerifiedGarbage.Proof.MlKem.X86_64.XeX

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_expand_ek`, constant time and its contract

Untrusted: everything here is checked by Lean. Everything but the sampling
of `Â` depends only on the pointers; the sampling leaks only `ρ`
(`Enc.mat_tr`); so the function leaks only the pointers and `ρ`
(`expandEk_ct`), and meets the shared contract (`expandEk_verified`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace ExpandEk

open VG.Impl.MlKem.X86_64.ExpandEk

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 expandEkK.pre expandEkK.pub I

theorem xh_lrel {σ₁ σ₂ x y : State} (p₁ : expandEkK.pre σ₁) (p₂ : expandEkK.pre σ₂) (pub : expandEkK.pub σ₁ σ₂)
    (h₁ : XC σ₁ x) (h₂ : XC σ₂ y) : LRel xeR xeW x y := by
  obtain ⟨e1, e2, e3, e4, _⟩ := pub
  refine ⟨xeLay p₁ h₁.top, xeLay p₂ h₂.top, fa3 ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e4]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rdx) (by decide), h₂.top.regs (.rbx, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trL {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12]) c h).isSome = true) :
    RelCT isa (LRel xeR xeW) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12] (fun x y h =>
    fa3 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.rbp, 0)) (l := 1) (by decide))
      (h.eq (p := (.r12, 0)) (l := 1) (by decide))) ht

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rdx, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa3 pub.2.2.1 pub.1 pub.2.1) (by taint_decide)

theorem hashes_tr : RelCT isa (R fun σ s => XC σ s ∧ s.gpr .r15 = 1) hash fun _ _ => True := by
  refine rel2_of (Q := LRel xeR xeW) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => xh_lrel p₁ p₂ pub h₁.1 h₂.1
  unfold VG.Impl.MlKem.X86_64.ExpandEk.hash
  exact RelCT.seq (LRel.step xeB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy16_okL Lx (dst := (.r12, 0)) (src := (.rbp, 0)) (n := 74) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (hash_tr xeB_bases (ps := [((.rbp, 0), 1184)]) (rate := 136) (out := (.r12, oXH)) (len := 32) (by decide)
      (show 6 < 256 by decide))

theorem EIn.any {σ : State} {E : Ptr} {ek m r : List Byte} {s : State} (h : Enc.EIn (xeC σ) E ek m r s) :
    Enc.EIn xeCA E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem copyRho_taint : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 0 + 1152) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 0 + 1152) 32))).isSome = true := by
  taint_decide

theorem rho_pub {σ₁ σ₂ : State} (pub : expandEkK.pub σ₁ σ₂) : Enc.rhoE (xeEk σ₁) = Enc.rhoE (xeEk σ₂) :=
  pub.2.2.2.2

theorem mat_tr (v : Sample4Impl) : RelCT isa (R XI) (Encrypt.mat v.callee (.rbp, 0)) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel xeR xeW x y ∧ Enc.EIρ xeCA (.rbp, 0) ρ x ∧
      Enc.EIρ xeCA (.rbp, 0) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc.mat_tr v (C := xeCA) xeMatChk xeSampChks copyRho_taint (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, ⟨⟨m₁, r₁, h₁⟩, e₁⟩, ⟨⟨m₂, r₂, h₂⟩, e₂⟩⟩
  exact ⟨Enc.rhoE (xeEk σ₁), xh_lrel p₁ p₂ pub h₁.out.2.xc h₂.out.2.xc, ⟨_, _, _, rfl, EIn.any h₁, e₁⟩,
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂, e₂⟩⟩

/-- After the sampling, and the test of its result. -/
abbrev XBF (σ s : State) : Prop := (∃ m r, Enc.EB (xeC σ) (.rbp, 0) (xeEk σ) m r 9 s) ∧ (s.gpr .r15).setWidth 32 ≠ 0

theorem matOut_tr : RelCT isa (R XBF) (matOut .r12) fun _ _ => True :=
  rel2_of (Q := LRel xeR xeW) (trL (by taint_decide))
    fun _ _ _ _ p₁ p₂ pub ⟨⟨_, _, h₁⟩, _⟩ ⟨⟨_, _, h₂⟩, _⟩ => xh_lrel p₁ p₂ pub h₁.i.out.2.xc h₂.i.out.2.xc

theorem r15_pub {σ₁ σ₂ x y : State} (pub : expandEkK.pub σ₁ σ₂) (h₁ : XB σ₁ x) (h₂ : XB σ₂ y) :
    x.gpr .r15 = y.gpr .r15 := by
  obtain ⟨_, _, h₁⟩ := h₁
  obtain ⟨_, _, h₂⟩ := h₂
  rw [h₁.r15, h₂.r15, rho_pub pub]

theorem body_tr : RelCT isa (R XB) (ifOk (matOut .r12)) (R XEnd) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono (relInv (I := XBF) (fun σ s hp ⟨⟨_, _, h⟩, hne⟩ => matOut_ok hp h hne) matOut_tr)
      (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, ⟨m₁, r₁, h₁⟩, ⟨m₂, r₂, h₂⟩⟩, hx, hy, hne⟩ => ?_) fun _ _ h => h
    have hne' : (y₀.gpr .r15).setWidth 32 ≠ 0 := by
      rw [← r15_pub pub ⟨_, _, h₁⟩ ⟨_, _, h₂⟩]; exact hne
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨⟨_, _, EB.flag' h₁ hx⟩, by rw [hx.cs .r15 (by decide)]; exact hne⟩,
      ⟨⟨_, _, EB.flag' h₂ hy⟩, by rw [hy.cs .r15 (by decide)]; exact hne'⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, ⟨m₁, r₁, h₁⟩, ⟨m₂, r₂, h₂⟩⟩, hx, hy, he⟩
    have he' : (y₀.gpr .r15).setWidth 32 = 0 := by rw [← r15_pub pub ⟨_, _, h₁⟩ ⟨_, _, h₂⟩]; exact he
    exact ⟨σ₁, σ₂, p₁, p₂, pub, skip_end (EB.flag' h₁ hx) (by rw [hx.cs .r15 (by decide)]; exact he),
      skip_end (EB.flag' h₂ hy) (by rw [hy.cs .r15 (by decide)]; exact he')⟩

theorem epi_tr : RelCT isa (R XEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.xh.xc.top.regs (.rbx, .rdx) (by decide), h₂.xh.xc.top.regs (.rbx, .rdx) (by decide), pub.2.2.1])
    (by taint_decide)

end ExpandEk

open ExpandEk in
theorem expandEk_ct (v : Sample4Impl) :
    ConstantTime isa expandEkK.pre expandEkK.pub (Impl.MlKem.X86_64.expandEk v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem.X86_64.expandEk
  refine RelCT.seq (relInv (I' := fun σ s => XC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := XI) (fun σ s hp hs => hashes_ok hp hs.1 hs.2) hashes_tr) ?_
  refine RelCT.seq (relInv (I' := XB) (fun σ s hp ⟨⟨m, r, h⟩, h15⟩ =>
    WP.mono (Enc.mat_ok v xeMatChk xeSampChks h h15) fun _ h' => ⟨m, r, h'⟩) (mat_tr v)) ?_
  exact RelCT.seq body_tr (RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

/-- A state satisfying `expandEkContract`'s precondition. -/
def expandEkSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1184⟩]
  wr := [⟨0x2000, 10432⟩, ⟨0x10000, 32768⟩]

theorem expandEk_verified (v : Sample4Impl) :
    Verified X86_64.target (Impl.MlKem.X86_64.expandEk v.callee) (Spec.MlKem.expandEkContract X86_64.abi 32) :=
  Verified.of_correct (expandEk_correct v) (expandEk_ct v)
    { pre := by
        intro s h
        sig_pre [Spec.MlKem.expandEkContract, Spec.MlKem.expandEkSig, X86_64.abi, VG.X86_64.argRegs] at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.expandEkContract, Spec.MlKem.expandEkSig, expandEkK, X86_64.abi, VG.X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.expandEkContract, Spec.MlKem.expandEkSig, expandEkK, X86_64.abi, VG.X86_64.argRegs]
          at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.expandEkContract, Spec.MlKem.expandEkSig, expandEkK, X86_64.abi,
        VG.X86_64.argRegs] [expandEkSat] using expandEkSat }

end VG.Proof.MlKem.X86_64
