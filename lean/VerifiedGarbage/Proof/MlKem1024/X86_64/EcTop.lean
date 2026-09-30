import VerifiedGarbage.Proof.MlKem1024.X86_64.EcBase

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_encaps`

Untrusted: everything here is checked by Lean. The function, piece by
piece: it returns 1 with `ML-KEM.Encaps_internal(ek, m)` in `key` and `ct`
if every `SampleNTT` succeeded within 280 iterations (`allOk4`), and 0
otherwise (`encaps1024_correct`); it leaks only the pointers and `ρ`
(`encaps1024_ct`); so it meets the shared contract (`encaps1024_verified`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Encaps4

open VG.Impl.MlKem1024.X86_64.Encaps1024

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := Enc4.EOut (ecC σ) (.r14, 0) (ecEk σ) (ecMs σ) (ecG σ).2 s

/-- At the end: `r15` as `allOk4`, `K` in `key`, and the ciphertext in `ct` if `r15` is 1. -/
structure ECEnd (σ s : State) : Prop where
  ec : EC σ s
  r15 : s.gpr .r15 = if allOk4 (Enc4.rhoE (ecEk σ)) 16 then 1 else 0
  key : bytesAt s.mem (pa s (.r12, 0)) 32 = (ecG σ).1
  ct : allOk4 (Enc4.rhoE (ecEk σ)) 16 →
    bytesAt s.mem (pa s (.r13, 0)) 1568 = ct1024 (aHat (Enc4.rhoE (ecEk σ))) (ecEk σ) (ecMs σ) (ecG σ).2

theorem out_ok {σ : State} {s : State} (h : EncO σ s) : WP isa out s (ECEnd σ) := by
  have hp := h.out.1
  have L := h.out.2.ec.lay hp
  unfold out
  refine WP.seq (WP.mono (copy_okL L (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.out.2.ec.step hp hP₁.b (by decide)
  have L₁ := k₁.lay hp
  refine WP.mono (copy_okL L₁ (dst := (.r13, 0)) (src := sc oCT4) (n := 1568) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step hp hP₂.b (by decide)
  refine ⟨k₂, ?_, ?_, fun ho => ?_⟩
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]; exact h.r15
  · rw [L₁.keepBytes hP₂.b (by decide), hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [hP₂.pa (by decide), hb₂, L.keepBytes hP₁.b (by decide)]; exact h.ct ho

theorem ECEnd.hin {σ s : State} (hp : encaps1024K.pre σ) (h : ECEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB ecB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (h.ec.lay hp).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the outputs. -/
theorem post_of {σ s : State} (h : ECEnd σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : encaps1024K.post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.ec.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rcx := by
    rw [pa, h.ec.top.regs (.r13, .rcx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk4 (Enc4.rhoE (ecEk σ)) 16
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show encapsInternal mlKem1024 minIterations _ _ = _
    rw [encapsInternal1024, kpkeEncrypt1024_some (a := aHat (Enc4.rhoE (ecEk σ))) fun i hi j hj => aHat4_eq ho hi hj,
      Option.map_some, hm, ← e12, ← e13, h.key, h.ct ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk4 ho
    show encapsInternal mlKem1024 minIterations _ _ = _
    rw [encapsInternal1024, kpkeEncrypt1024_none hi hj hn]
    rfl

end Encaps4

open Encaps4 in
theorem encaps1024_correct (σ : State) (hp : encaps1024K.pre σ) :
    ∃ t s', Exec isa encaps1024 σ t s' ∧ abiPreserved σ s' ∧ encaps1024K.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (hashes_ok hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (Enc4.encrypt_ok (C := ecC σ) ecEncChk h₂.1 h₂.2) fun s₃ h₃ =>
        WP.seq (WP.mono (out_ok h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.ec.top (h₄.hin hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of h₄ hr hm⟩ : gprPreserved σ s₅ ∧ encaps1024K.post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Encaps4

open VG.Impl.MlKem1024.X86_64.Encaps1024

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 encaps1024K.pre encaps1024K.pub I

theorem ec_lrel {σ₁ σ₂ x y : State} (p₁ : encaps1024K.pre σ₁) (p₂ : encaps1024K.pre σ₂) (pub : encaps1024K.pub σ₁ σ₂)
    (h₁ : EC σ₁ x) (h₂ : EC σ₂ y) : LRel ecR ecW x y := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := pub
  refine ⟨h₁.lay p₁, h₂.lay p₂, fa5 ?_ ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.r14, .rdi) (by decide), h₂.top.regs (.r14, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbp, .rsi) (by decide), h₂.top.regs (.rbp, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rcx) (by decide), h₂.top.regs (.r13, .rcx) (by decide), e4]

theorem rho_pub {σ₁ σ₂ : State} (pub : encaps1024K.pub σ₁ σ₂) : Enc4.rhoE (ecEk σ₁) = Enc4.rhoE (ecEk σ₂) :=
  pub.2.2.2.2.2.2

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trL {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) c h).isSome = true) :
    RelCT isa (LRel ecR ecW) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r13, .r14] (fun x y h =>
    fa5 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.rbp, 0)) (l := 1) (by decide))
      (h.eq (p := (.r12, 0)) (l := 1) (by decide)) (h.eq (p := (.r13, 0)) (l := 1) (by decide))
      (h.eq (p := (.r14, 0)) (l := 1) (by decide))) ht

theorem hashes_trL : RelCT isa (LRel ecR ecW) hashes fun _ _ => True := by
  unfold hashes
  refine RelCT.seq (LRel.step ecB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step ecB_bases (hash_tr ecB_bases (ps := [((.r14, 0), 1568)]) (rate := 136)
      (out := sc oH) (len := 32) (by decide) (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok ecB_bases (ps := [((.r14, 0), 1568)]) (rate := 136) (out := sc oH) (len := 32)
        (by decide) (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr ecB_bases (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64) (by decide)
      (show 6 < 256 by decide)))

theorem hashes_tr : RelCT isa (R fun σ s => EC σ s ∧ s.gpr .r15 = 1) hashes fun _ _ => True :=
  rel2_of hashes_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel p₁ p₂ pub h₁.1 h₂.1

theorem EIn.any {σ : State} {E : Ptr} {ek m r : List Byte} {s : State} (h : Enc4.EIn (ecC σ) E ek m r s) :
    Enc4.EIn ecCA E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem copyRho_taint : (taint.check (X86_64.Taint.ofRegs [.rbx, .r14]) (copy (sc oSB) (.r14, 0 + 1536) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx, .r14]) (copy (sc oSB) (.r14, 0 + 1536) 32))).isSome = true := by
  taint_decide

theorem encrypt_tr : RelCT isa (R EncI) (encrypt1024 (.r14, 0)) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel ecR ecW x y ∧ Enc4.EIρ ecCA (.r14, 0) ρ x ∧
      Enc4.EIρ ecCA (.r14, 0) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc4.encrypt_tr (C := ecCA) ecEncChk copyRho_taint (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc4.EIρ ecCA (.r14, 0) (Enc4.rhoE (ecEk σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc4.EIρ ecCA (.r14, 0) (Enc4.rhoE (ecEk σ₁)) y := ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc4.rhoE (ecEk σ₁), ec_lrel p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr : RelCT isa (R EncO) out fun _ _ => True := by
  refine rel2_of (Q := LRel ecR ecW) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec
  unfold out
  exact RelCT.seq (LRel.step ecB_bases (trL (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩) (trL (by taint_decide))

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.r8, .rsi, .rdx, .rcx, .rdi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.2.1 pub.2.2.1 pub.2.2.2.1 pub.1) (by taint_decide)

theorem epi_tr : RelCT isa (R ECEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.ec.top.regs (.rbx, .r8) (by decide), h₂.ec.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

end Encaps4

open Encaps4 in
theorem encaps1024_ct : ConstantTime isa encaps1024K.pre encaps1024K.pub encaps1024 := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold encaps1024
  refine RelCT.seq (relInv (I' := fun σ s => EC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := EncI) (fun σ s hp hs => hashes_ok hp hs.1 hs.2) hashes_tr) ?_
  refine RelCT.seq (relInv (I' := EncO) (fun σ s _ hs => Enc4.encrypt_ok (C := ecC σ) ecEncChk hs.1 hs.2)
    encrypt_tr) ?_
  refine RelCT.seq (relInv (I' := ECEnd) (fun σ s _ hs => out_ok hs) out_tr) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

/-- A state satisfying `encapsContract`'s precondition. -/
def encaps1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem encaps1024_verified :
    Verified X86_64.target encaps1024 (Spec.MlKem1024.encapsContract X86_64.abi 32) :=
  Verified.of_correct encaps1024_correct encaps1024_ct
    { pre := by sig_implies_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encaps1024K, X86_64.abi,
        VG.X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encaps1024K, X86_64.abi,
        VG.X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encaps1024K, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encaps1024K, X86_64.abi,
        VG.X86_64.argRegs] [encaps1024Sat] using encaps1024Sat }

end VG.Proof.MlKem1024.X86_64
