import VerifiedGarbage.Proof.MlKem.X86_64.EcBase

/-!
# ML-KEM on x86-64: encapsulation

The function, piece by piece: it returns 1 with `ML-KEM.Encaps_internal(ek,
m)` in `key` and `ct` if every `SampleNTT` succeeded within 280 iterations
(`allOk`), and 0 otherwise (`kemEncaps_correct`); it leaks only the pointers
and `ρ` (`kemEncaps_ct`). Each parameter set's file moves this to its shared
contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable {L : Kem} (W : EcWf L)

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := Enc.EOut L (ecC W σ) (.r14, 0) (ecEk L σ) (ecMs σ) (ecG L σ).2 s

/-- At the end: `r15` as `allOk`, `K` in `key`, and the ciphertext in `ct` if `r15` is 1. -/
structure ECEnd (L : Kem) (σ s : State) : Prop where
  ec : EC L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (ecEk L σ)) (L.k * L.k) then 1 else 0
  key : bytesAt s.mem (pa s (.r12, 0)) 32 = (ecG L σ).1
  ct : allOk L.k (Enc.rhoE L (ecEk L σ)) (L.k * L.k) →
    bytesAt s.mem (pa s (.r13, 0)) L.ctLen = KPke.ct L.p (aHat (Enc.rhoE L (ecEk L σ))) (ecEk L σ) (ecMs σ) (ecG L σ).2

include W

theorem out_ok {σ : State} {s : State} (h : EncO W σ s) : WP isa (out L) s (ECEnd L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay W hp
  unfold out
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.out.2.ec.step W hp hP₁.b W.o₁K
  have L₁ := k₁.lay W hp
  refine WP.mono (copy_okL L₁ (dst := (.r13, 0)) (src := sc L.oCT) (n := L.ctLen) (show Reg.rbx ≠ .rdi by decide) W.o₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.o₂K
  refine ⟨k₂, ?_, ?_, fun ho => ?_⟩
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]; exact h.r15
  · rw [L₁.keepBytes hP₂.b W.o₂G, hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [hP₂.pa (by decide), hb₂, L₀.keepBytes hP₁.b W.o₁C]; exact h.ct ho

theorem ECEnd.hin {σ s : State} (hp : (encapsK L).pre σ) (h : ECEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.ec.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the outputs. -/
theorem post_of {σ s : State} (h : ECEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (encapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.ec.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rcx := by
    rw [pa, h.ec.top.regs (.r13, .rcx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (Enc.rhoE L (ecEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := aHat (Enc.rhoE L (ecEk L σ)))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, h.key, h.ct ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

end Encaps

open Encaps in
theorem kemEncaps_correct (v : Sample4Impl) {L : Kem} (W : EcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    (hctl : ctlOk (kemEncaps L v.callee) = true) (σ : State) (hp : (encapsK L).pre σ) :
    ∃ t s', Exec isa (kemEncaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (encapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (hashes_ok W hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (Enc.encrypt_ok v K W.k (C := ecC W σ) W.enc h₂.1 h₂.2) fun s₃ h₃ =>
        WP.seq (WP.mono (out_ok W h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.ec.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (encapsK L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable {L : Kem} (W : EcWf L)

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (encapsK L).pre (encapsK L).pub I

include W

theorem ec_lrel {σ₁ σ₂ x y : State} (p₁ : (encapsK L).pre σ₁) (p₂ : (encapsK L).pre σ₂)
    (pub : (encapsK L).pub σ₁ σ₂) (h₁ : EC L σ₁ x) (h₂ : EC L σ₂ y) : LRel (ecR L) (ecW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa5 ?_ ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.r14, .rdi) (by decide), h₂.top.regs (.r14, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbp, .rsi) (by decide), h₂.top.regs (.rbp, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rcx) (by decide), h₂.top.regs (.r13, .rcx) (by decide), e4]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (encapsK L).pub σ₁ σ₂) : Enc.rhoE L (ecEk L σ₁) = Enc.rhoE L (ecEk L σ₂) :=
  pub.2.2.2.2.2.2

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trL {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) c h).isSome = true) :
    RelCT isa (LRel (ecR L) (ecW L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r13, .r14] (fun _ _ h =>
    fa5 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2.2)) ht

theorem hashes_trL : RelCT isa (LRel (ecR L) (ecW L)) (hashes L) fun _ _ => True := by
  unfold hashes
  obtain ⟨_, hT⟩ := W.hT
  refine RelCT.seq (LRel.step (ecB_bases L) (trL W hT) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (ecB_bases L) (hash_tr (ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136)
      (out := sc oH) (len := 32) W.h₂ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32)
        W.h₂ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64) W.h₃
      (show 6 < 256 by decide)))

theorem hashes_tr : RelCT isa (R L fun σ s => EC L σ s ∧ s.gpr .r15 = 1) (hashes L) fun _ _ => True :=
  rel2_of (hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel W p₁ p₂ pub h₁.1 h₂.1

omit W in
theorem EIn.any {W : EcWf L} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State} (h : Enc.EIn L (ecC W σ) E ek m r s) :
    Enc.EIn L (ecCA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (EncI W)) (encrypt L v.callee (.r14, 0)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR L) (ecW L) x y ∧ Enc.EIρ L (ecCA W) (.r14, 0) ρ x ∧
      Enc.EIρ L (ecCA W) (.r14, 0) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := ecCA W) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (ecCA W) (.r14, 0) (Enc.rhoE L (ecEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (ecCA W) (.r14, 0) (Enc.rhoE L (ecEk L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (ecEk L σ₁), ec_lrel W p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr : RelCT isa (R L (EncO W)) (out L) fun _ _ => True := by
  refine rel2_of (Q := LRel (ecR L) (ecW L)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ec_lrel W p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec
  unfold out
  obtain ⟨_, oT₁⟩ := W.oT₁
  obtain ⟨_, oT₂⟩ := W.oT₂
  exact RelCT.seq (LRel.step (ecB_bases L) (trL W oT₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
        fun _ h => ⟨_, h.1⟩) (trL W oT₂)

omit W in
theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.r8, .rsi, .rdx, .rcx, .rdi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.2.1 pub.2.2.1 pub.2.2.2.1 pub.1) (by taint_decide)

omit W in
theorem epi_tr : RelCT isa (R L (ECEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.ec.top.regs (.rbx, .r8) (by decide), h₂.ec.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

end Encaps

open Encaps in
theorem kemEncaps_ct (v : Sample4Impl) {L : Kem} (W : EcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    ConstantTime isa (encapsK L).pre (encapsK L).pub (kemEncaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps
  refine RelCT.seq (relInv (I' := fun σ s => EC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := EncI W) (fun σ s hp hs => hashes_ok W hp hs.1 hs.2) (hashes_tr W)) ?_
  refine RelCT.seq (relInv (I' := EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.k (C := ecC W σ) W.enc hs.1 hs.2)
    (encrypt_tr W v K)) ?_
  refine RelCT.seq (relInv (I' := ECEnd L) (fun σ s _ hs => out_ok W hs) (out_tr W)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
