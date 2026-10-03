import VerifiedGarbage.Proof.MlKem.X86_64.KgB

/-!
# ML-KEM on x86-64: key generation, constant time of the pieces

Two runs from entry states that agree on the public data (`keyGenK.pub`: the
pointers, the stack pointer and `ρ`), each at the same step with its invariant
(`Rel2`), are in the same layout (`kc_lrel`), and each piece leaks the same in
both (`gRho_tr`, `samples_tr`, `se_tr`, `row_tr`, `encS_tr`, `fin_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A piece's constant time in a relation implied by the invariants of two runs. -/
theorem rel2_of {Pre : State → Prop} {Pub : State → State → Prop} {I : State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable {L : Kem} (W : KgWf L)
include W

theorem kc_lrel {σ₁ σ₂ x y : State} (p₁ : (keyGenK L).pre σ₁) (p₂ : (keyGenK L).pre σ₂) (pub : (keyGenK L).pub σ₁ σ₂)
    (h₁ : KC σ₁ x) (h₂ : KC σ₂ y) : LRel kgR (kgW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (keyGenK L).pub σ₁ σ₂) : rhoK L σ₁ = rhoK L σ₂ := pub.2.2.2.2.2

/-! ## `G` -/

theorem gRho_trL : RelCT isa (LRel kgR (kgW L)) (gRho L) fun _ _ => True := by
  unfold gRho
  refine RelCT.seq (LRel.step (kgB_bases L) (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) W.nbT)
    fun x Lx => WP.mono (setB_okL Lx (by decide) (by have := W.k; omega) (p := sc oNB) (v := L.k) W.nb)
      fun _ h => ⟨_, h.1⟩) (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L)
        (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG) (len := 64) W.gH (show 6 < 256 by decide))
    fun x Lx => WP.mono (hash_ok (kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
      (len := 64) W.gH (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) (by taint_decide)))

theorem gRho_tr : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub fun σ s => KC σ s ∧ s.gpr .r15 = 1) (gRho L)
    fun _ _ => True :=
  rel2_of (gRho_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.1 h₂.1

/-! ## The matrix -/

theorem sample_tr {e : Nat} (he : e < L.k * L.k) (he' : 4 * (L.k * L.k / 4) ≤ e) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e)) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      fun _ _ => True := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  exact rel2_of (sampleIJ_tr (kgB_bases L) rbx_na (by have := div_lt_k he; omega) (by have := mod_lt_k he; omega)
      hc.1.1.1.1.1 (W.ijT e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact rho_pub pub⟩

theorem quad_trK (v : Sample4Impl) {q : Nat} (hq : q < L.k * L.k / 4) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (4 * q)))
      (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) fun _ _ => True := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2
  exact rel2_of (RelCT.exists_ fun ρ => quad_tr (ρ := ρ) v (kgB_bases L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < L.k * L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < L.k * L.k by omega); omega⟩) hc.1.1.1.1.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨KPke.kgRho L.p (kgD σ₁), kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr (v : Sample4Impl) : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L 0)) (L.samples v.callee)
    (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (L.k * L.k))) :=
  samples_tr' L v.callee (R := fun e => Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e))
    (fun _ he he' => relInv (fun _ _ hp hs => sample_step W hp he he' hs) (sample_tr W he he'))
    (fun _ hq => relInv (fun _ _ hp hs => quad_step v W hp hq hs) (quad_trK W v hq))

/-! ## `ŝ` and `ê` -/

theorem prfs_trK (v : Sample4Impl) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest0 L)) (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW)
      fun _ _ => True := by
  have hc := W.prfs
  simp only [prfsKChk, Bool.and_eq_true] at hc
  exact rel2_of (v.prfs_tr (kgB_bases L) (by have := W.k; omega) hc.1.1.1.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem se_tr {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L N 0 0)) (se L A N) fun _ _ => True := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, _⟩ := hc
  unfold se
  refine rel2_of (Q := fun x y => LRel kgR (kgW L) x y ∧ True ∧ True)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS N))) (kgB_bases L)
      (RelCT.mono (cbd2At_trL rbx_na htw) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx _ => WP.mono (cbd2At_okL Lx rbx_na htw) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hA hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, trivial, trivial⟩

/-! ## The rows of `ek` -/

theorem row_tr {A : Arith} (hA : ArithOk A) {i : Nat} (hi : i < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L (2 * L.k) i 0)) (row L A i) fun _ _ => True := by
  have hc := W.row i hi
  simp only [rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, _⟩ := hc
  unfold row
  refine rel2_of (Q := fun x y => LRel kgR (kgW L) x y ∧ (DotIn (fun j => L.aS i j) pS L.k x ∧
      Reduced x.mem (pa x (pS (L.k + i)))) ∧ (DotIn (fun j => L.aS i j) pS L.k y ∧
        Reduced y.mem (pa y (pS (L.k + i)))))
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS (L.k + i)))) (kgB_bases L)
      (RelCT.mono (dotN_tr hA (kgB_bases L) W.k.1 (dotChk_spec hdc)) (fun _ _ ⟨e, h₁, h₂⟩ => ⟨e, h₁.1, h₂.1⟩)
        fun _ _ h => h)
      (fun x Lx hx => ?_)
      (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (kgB_bases L) (addAt_tr rbx_na hac)
        (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
          ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (enc12At_trL r12_na htw)))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc,
      ⟨fun k hk => ⟨(h₁.matIJ hi hk).1, (h₁.se k (by omega)).1⟩, (h₁.se (L.k + i) (by omega)).1⟩,
      ⟨fun k hk => ⟨(h₂.matIJ hi hk).1, (h₂.se k (by omega)).1⟩, (h₂.se (L.k + i) (by omega)).1⟩⟩
  -- The sum of products, from reduced inputs.
  refine WP.mono (dotN_ok hA (kgB_bases L) W.k.1 (dotChk_spec hdc) Lx (a := fun k => polyAt x.mem (pa x (L.aS i k)))
    (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx.1 k hk).1, rfl⟩) (fun k hk => ⟨(hx.1 k hk).2, rfl⟩))
    fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk3 hx.2⟩

/-! ## The rows of `dk` -/

theorem encS_tr {j : Nat} (hj : j < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L (2 * L.k) L.k j)) (encS j) fun _ _ => True := by
  have hc := W.encS j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL r13_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.se j (by omega)).1, (h₂.se j (by omega)).1⟩

/-! ## The rest of the keys -/

theorem fin_trL : RelCT isa (LRel kgR (kgW L)) (fin L) fun _ _ => True := by
  unfold fin
  have tr : ∀ {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T},
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true →
      RelCT isa (LRel kgR (kgW L)) c fun _ _ => True := fun ht => taintRel [.rbx, .rbp, .r12, .r13] (fun x y h =>
    fa4 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2)) ht
  obtain ⟨_, t₁⟩ := W.finT₁
  obtain ⟨_, t₂⟩ := W.finT₂
  obtain ⟨_, t₄⟩ := W.finT₄
  refine RelCT.seq (LRel.step (kgB_bases L) (tr t₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (tr t₂) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
      (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136) (out := (.r13, 384 * L.k + L.ekLen))
        (len := 32) W.f₃ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (tr t₄)))

theorem fin_tr : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L (2 * L.k) L.k L.k)) (fin L) fun _ _ => True :=
  rel2_of (fin_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

end KeyGen

end VG.Proof.MlKem.X86_64
