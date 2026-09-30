import VerifiedGarbage.Proof.MlKem.X86_64.KgB

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, constant time of the pieces

Untrusted: everything here is checked by Lean. Two runs from entry states
that agree on the public data (`keyGenK.pub`: the pointers, the stack
pointer and `ρ`), each at the same step with its invariant (`Rel2`), are
in the same layout (`kc_lrel`), and each piece leaks the same in both
(`gRho_tr`, `samples_tr`, `se_tr`, `row_tr`, `encS_tr`, `fin_tr`).
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

variable {K : KPre}

theorem kc_lrel {σ₁ σ₂ x y : State} (p₁ : K.pre σ₁) (p₂ : K.pre σ₂) (pub : K.pub σ₁ σ₂)
    (h₁ : KC σ₁ x) (h₂ : KC σ₂ y) : LRel kgR kgW x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := K.eq pub
  refine ⟨h₁.lay p₁, h₂.lay p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

theorem rho_pub {σ₁ σ₂ : State} (pub : K.pub σ₁ σ₂) : rhoK σ₁ = rhoK σ₂ := (K.eq pub).2.2.2.2.2

/-! ## `G` -/

theorem setNB3_taint : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) 3)) (.block [])).isSome =
    true := by decide +kernel

theorem gRho_trL : RelCT isa (LRel kgR kgW) gRho fun _ _ => True := by
  unfold gRho
  refine RelCT.seq (LRel.step kgB_bases (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) (by decide)) setNB3_taint)
    fun x Lx => WP.mono (setB_okL Lx (by decide) (by decide) (p := sc oNB) (v := 3) (by decide))
      fun _ h => ⟨_, h.1⟩) (RelCT.seq (LRel.step kgB_bases (hash_tr kgB_bases (ps := [((.rbp, 0), 32), (sc oNB, 1)])
      (rate := 72) (out := sc oG) (len := 64) (by decide) (show 6 < 256 by decide))
    fun x Lx => WP.mono (hash_ok kgB_bases (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
      (len := 64) (by decide) (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) (by decide)) (by taint_decide)))

theorem gRho_tr : RelCT isa (Rel2 K.pre K.pub fun σ s => KC σ s ∧ s.gpr .r15 = 1) gRho
    fun _ _ => True :=
  rel2_of gRho_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel p₁ p₂ pub h₁.1 h₂.1

/-! ## The matrix -/

theorem setIJ_taint : ∀ e < 9, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (oSB + 32)) (e % 3) ++ setB (sc (oSB + 33)) (e / 3))) (.block [])).isSome = true := by
  decide +kernel

theorem sample_tr {e : Nat} (he : e < 9) :
    RelCT isa (Rel2 K.pre K.pub (KB e)) (sampleIJ (e / 3) (e % 3)) fun _ _ => True := by
  have hc := kbChk_all e he
  simp only [kbChk, Bool.and_eq_true] at hc
  exact rel2_of (sampleIJ_tr kgB_bases (by omega) (by omega) hc.1.1.1.1.1 (setIJ_taint e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact rho_pub pub⟩

theorem quad_trK (v : Sample4Impl) {e : Nat} (hc : kqChk e = true) (he : e + 4 ≤ 9) :
    RelCT isa (Rel2 K.pre K.pub (KB e)) (quad v.callee 3 e (sc (oP (6 + e))) (pS 17))
      fun _ _ => True := by
  simp only [kqChk, Bool.and_eq_true] at hc
  exact rel2_of (RelCT.exists_ fun ρ => quad_tr (ρ := ρ) v kgB_bases (by omega) (fun k hk => ⟨by omega, by omega⟩)
      hc.1.1.1.1.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kgRho (kgD σ₁), kc_lrel p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr (v : Sample4Impl) : RelCT isa (Rel2 K.pre K.pub (KB 0)) (samples v.callee)
    (Rel2 K.pre K.pub (KB 9)) := by
  unfold samples
  exact RelCT.seq (relInv (fun σ s hp hs => quad_step v hp kqChk_all.1 (by decide) hs)
    (quad_trK v kqChk_all.1 (by decide))) (RelCT.seq (relInv (fun σ s hp hs => quad_step v hp kqChk_all.2
      (by decide) hs) (quad_trK v kqChk_all.2 (by decide)))
    (relInv (fun σ s hp hs => sample_step hp (by decide) hs) (sample_tr (by decide))))

/-! ## `ŝ` and `ê` -/

theorem setNB_taint : ∀ N < 7, (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) N))
    (.block [])).isSome = true := by
  decide +kernel

theorem se_tr {N : Nat} (hN : N < 6) :
    RelCT isa (Rel2 K.pre K.pub (KRest N 0 0)) (se N) fun _ _ => True := by
  have hc := seChk_all N hN
  simp only [seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hpc, hic⟩, _⟩ := hc
  unfold se
  refine rel2_of (Q := fun x y => LRel kgR kgW x y ∧ True ∧ True) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS N)))
    kgB_bases (RelCT.mono (prfCbd_tr kgB_bases (by omega) hpc (setNB_taint N (by omega))) (fun _ _ h => h.1)
      fun _ _ h => h)
    (fun x Lx _ => WP.mono (prfCbd_ok Lx kgB_bases (by omega) hpc) fun x' ⟨hP, hq⟩ =>
      ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel p₁ p₂ pub h₁.kc h₂.kc, trivial, trivial⟩

/-! ## The rows of `ek` -/

theorem row_tr {i : Nat} (hi : i < 3) :
    RelCT isa (Rel2 K.pre K.pub (KRest 6 i 0)) (row i) fun _ _ => True := by
  have hc := rowChk_all i hi
  simp only [rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, _⟩ := hc
  unfold row
  refine rel2_of (Q := fun x y => LRel kgR kgW x y ∧ (DotIn (fun j => aS i j) pS x ∧
      Reduced x.mem (pa x (pS (3 + i)))) ∧ (DotIn (fun j => aS i j) pS y ∧ Reduced y.mem (pa y (pS (3 + i)))))
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS (3 + i)))) kgB_bases
      (RelCT.mono (dotAt_tr kgB_bases hdc) (fun _ _ ⟨e, h₁, h₂⟩ => ⟨e, h₁.1, h₂.1⟩) fun _ _ h => h)
      (fun x Lx hx => ?_)
      (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) kgB_bases (addAt_tr rbx_na hac)
        (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
          ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (enc12At_trL r12_na htw)))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel p₁ p₂ pub h₁.kc h₂.kc,
      ⟨fun k hk => ⟨(h₁.mat i hi k hk).1, (h₁.se k (by omega)).1⟩, (h₁.se (3 + i) (by omega)).1⟩,
      ⟨fun k hk => ⟨(h₂.mat i hi k hk).1, (h₂.se k (by omega)).1⟩, (h₂.se (3 + i) (by omega)).1⟩⟩
  -- The sum of products, from reduced inputs.
  refine WP.mono (dotAt_ok Lx kgB_bases hdc (a := fun k => polyAt x.mem (pa x (aS i k)))
    (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx.1 k hk).1, rfl⟩) (fun k hk => ⟨(hx.1 k hk).2, rfl⟩))
    fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk3 hx.2⟩

/-! ## The rows of `dk` -/

theorem encS_tr {j : Nat} (hj : j < 3) :
    RelCT isa (Rel2 K.pre K.pub (KRest 6 3 j)) (encS j) fun _ _ => True := by
  have hc := encSChk_all j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL r13_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel p₁ p₂ pub h₁.kc h₂.kc, (h₁.se j (by omega)).1, (h₂.se j (by omega)).1⟩

/-! ## The rest of the keys -/

theorem fin_trL : RelCT isa (LRel kgR kgW) fin fun _ _ => True := by
  unfold fin
  have tr : ∀ {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T},
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true →
      RelCT isa (LRel kgR kgW) c fun _ _ => True := fun ht => taintRel [.rbx, .rbp, .r12, .r13] (fun x y h =>
    fa4 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.rbp, 0)) (l := 1) (by decide))
      (h.eq (p := (.r12, 0)) (l := 1) (by decide)) (h.eq (p := (.r13, 0)) (l := 1) (by decide))) ht
  refine RelCT.seq (LRel.step kgB_bases (tr (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 1152)) (src := sc oG) (n := 32) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step kgB_bases (tr (by taint_decide)) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 1152)) (src := (.r12, 0)) (n := 1184) (by decide) (by decide))
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step kgB_bases (hash_tr kgB_bases (ps := [((.r12, 0), 1184)]) (rate := 136)
      (out := (.r13, 2336)) (len := 32) (by decide) (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok kgB_bases (ps := [((.r12, 0), 1184)]) (rate := 136) (out := (.r13, 2336)) (len := 32)
        (by decide) (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (tr (by taint_decide))))

theorem fin_tr : RelCT isa (Rel2 K.pre K.pub (KRest 6 3 3)) fin fun _ _ => True :=
  rel2_of fin_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel p₁ p₂ pub h₁.kc h₂.kc

end KeyGen

end VG.Proof.MlKem.X86_64
