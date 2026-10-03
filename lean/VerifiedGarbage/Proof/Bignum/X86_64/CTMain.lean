import VerifiedGarbage.Proof.Bignum.X86_64.CTSetup

/-!
# `vg_rsa_public` on x86-64: constant time but for `n` and `e`

The result's store (`out_ct`), `main` (`main_ct`) and the whole function
(`code_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## The result -/

/-- The public data of the result: the working space, the length `k` and `out`. -/
structure OPub where
  L : Lay
  k : Nat
  op : Addr

/-- `outPhase_ok`'s hypotheses. -/
def OPre (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Good s p.L.B p.L.Z p.L.w p.L.minv ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ word s.mem p.L.B (8 * sOut) = p.op ∧ word s.mem p.L.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.L.B (8 * sMask) = mask c ∧ (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- Before `storeBE`. -/
def O1 (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Scr s p.L.B p.L.Z ∧ s.gpr .rdi = p.L.B ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .rbx = off p.L.B (slot p.L.w aY) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = mask c ∧
    (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- The result's store leaks the same in runs with the same working space,
length and `out`. -/
theorem out_ct : RelCT isa (Two OPre) (seqs outSteps) fun _ _ => True := by
  unfold outSteps
  refine RelCT.seq (two_piece (Ψ := O1) [.rdi] (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.L.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega)
    refine WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aY) ∧ t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
        t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
        hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) rfl)
      fun t ⟨⟨hbx, hsi, hcx, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hw, hZ,
        hk1, hk, hbx, hsi, hcx, h15, fun j hj => by rw [k.2.2]; exact hout j hj, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.L.B) [.rbx, .rsi, .rcx]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, hdi, hw, hZ, hk1, hk, hbx, hsi, hcx, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs hbx hsi hcx h15 hk1 hk hw
      (by have := slot_le (w := p.L.w) (show aY < 8 by decide); omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## Sequences and re-indexing -/

theorem exec_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

theorem RelCT.seqs_append {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_append ha hb e₁) (exec_seqs_append ha hb e₂)

/-- Two runs related with the same `a` are related with the same `b`. -/
theorem two_bind {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop}
    (f : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∃ b, Ψ b s₁ ∧ Ψ b s₂) {s₁ s₂ : State} (h : Two Φ s₁ s₂) :
    Two Ψ s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := h; f a s₁ s₂ h₁ h₂

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, the pointers, `e`'s
length and the bytes of `n` and `e`. -/
structure MPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  ep : Addr
  ip : Addr
  len : Nat
  nb : List Byte
  eb : List Byte

abbrev MPub.w (p : MPub) : Nat := (p.k + 7) / 8
abbrev MPub.N (p : MPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `main_ok`'s hypotheses. -/
def MRel (p : MPub) (s : State) : Prop :=
  ∃ xb, MainPre s p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true

/-- After the setup. -/
def MA (p : MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t.mem ∧
    Keep mmRegs σ t

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem so_minv {t t' : State} {B : Addr} {Z w : Nat} {mi mi' : BitVec 64} {N X X' : Nat}
    (h : SetupOut t B Z w mi N X) (h' : SetupOut t' B Z w mi' N X') (hodd : N % 2 = 1) (hw : 1 ≤ w) :
    mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64} {X : Nat}, SetupOut t B Z w mi N X →
      (word t.mem B (slot w aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-- `main`'s state facts give the setup's. -/
theorem MRel.sh {p : MPub} {s : State} (h : MRel p s) : SH ⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ s := by
  obtain ⟨xb, h, hv⟩ := h
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact ⟨h.scr, h.rdi, h.z, show 9 ≤ p.k by omega, show p.k < 2 ^ 31 by omega, h.hK, h.hN, h.hIn, h.n, h.nl,
    hodd, xb, h.x, h.xl⟩

/-- The setup leaks the same in runs that agree on `n`. -/
theorem mainA_ct : RelCT isa (Two MRel) (seqs (loadSteps ++ restSteps)) (Two MA) := by
  refine two_post ((RelCT.seqs_append (by simp [loadSteps]) (by simp [restSteps])
    (RelCT.seq setupLoad_ct (two_map (fun p : SPub => (⟨p.B, p.Z, p.w⟩ : RPub)) (fun _ _ h => h.sr) setupRest_ct))).mono (fun _ _ h => two_bind (fun p _ _ h₁ h₂ =>
      ⟨_, h₁.sh, h₂.sh⟩) h) fun _ _ h => h) ?_
  rintro p s ⟨xb, h, hv⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact WP.mono (setup_ok h.scr h.rdi h.z (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
    fun t ⟨mi, so, f, k⟩ => ⟨s, xb, mi, h, hv, so, f, k⟩

/-- After `R² mod m`. -/
def MB (p : MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64) (t₁ : State),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t₁.mem ∧
    Keep mmRegs σ t₁ ∧ Good t p.B p.Z p.w mi ∧ wv t.mem p.B (slot p.w aR2) p.w < p.N ∧
    wv t.mem p.B (slot p.w aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N ∧
    Frm p.B (r2Ranges p.w) t₁.mem t.mem ∧ Keep mmRegs t₁ t

theorem MA.r2Pre {p : MPub} {t : State} {σ : State} {xb : List Byte} {mi : BitVec 64}
    (h : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true)
    (so : SetupOut t p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) : R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ t := by
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact ⟨⟨so.good, h.z⟩, show 2 ≤ p.w by unfold MPub.w; omega, show p.w < 2 ^ 30 by unfold MPub.w; omega, so.n, so.inv, so.r12, so.r10,
    hodd, hlo⟩

/-- `R² mod m` leaks the same in runs that agree on `n`. -/
theorem mainB_ct : RelCT isa (Two MA) (seqs (r2Steps Mont.base)) (Two MB) := by
  refine two_post ((r2_ct Mont.base).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
  · obtain ⟨σ₁, xb₁, mi₁, hm₁, hv, so₁, -⟩ := h₁
    obtain ⟨σ₂, xb₂, mi₂, hm₂, -, so₂, -⟩ := h₂
    obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
    have := hm₁.k1
    obtain rfl := so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
    exact ⟨_, MA.r2Pre hm₁ hv so₁, MA.r2Pre hm₂ hv so₂⟩
  rintro p t ⟨σ, xb, mi, hm, hv, so, f, k⟩
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv hm.k1
  have := hm.k1
  have := hm.k2
  exact WP.mono (r2_ok Mont.base so.good hm.z (by unfold MPub.w; omega) (by unfold MPub.w; omega) so.n so.inv so.r12 so.r10 hodd hlo)
    fun t' ⟨hg, hlt, hr, f', k'⟩ => ⟨σ, xb, mi, t, hm, hv, so, f, k, hg, hlt, hr, f', k'⟩

/-- What the exponentiation phase needs, from the facts after `R² mod m`. -/
theorem mb_ePre {p : MPub} {t σ t₁ : State} {xb : List Byte} {mi : BitVec 64}
    (hm : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true)
    (so : SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) (f : Frm p.B (setupRanges p.w) σ.mem t₁.mem)
    (k : Keep mmRegs σ t₁) (hg : Good t p.B p.Z p.w mi) (hlt : wv t.mem p.B (slot p.w aR2) p.w < p.N)
    (hr : wv t.mem p.B (slot p.w aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N)
    (f' : Frm p.B (r2Ranges p.w) t₁.mem t.mem) (k' : Keep mmRegs t₁ t) :
    EPhasePre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N, p.ep, p.len, p.eb⟩ t := by
  obtain ⟨hodd, hN1, -⟩ := valid_facts hv hm.k1
  have := hm.k1
  have := hm.k2
  have := hm.L2
  have hn := hm.scr.nowrap
  have hZ : slot p.w 8 ≤ p.Z := hm.z
  have hn' : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega
  have x₁₂ := (Fixed.of_frm f (setupRanges_fixed _)).trans (Fixed.of_frm f' (r2Ranges_fixed _))
  have i₁₂ := (InScr.of_frm f fun r hr => (setupRanges_le _ r hr).trans hZ).trans
    (InScr.of_frm f' fun r hr => (r2Ranges_le _ r hr).trans hZ)
  exact ⟨Spec.Rsa.os2ip xb, hg, hZ, show 2 ≤ p.w by unfold MPub.w; omega,
    show p.w < 2 ^ 31 by unfold MPub.w; omega, hodd, hN1,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n,
    by rw [f'.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one, hlt, hr,
    by rw [x₁₂ sE (by decide)]; exact hm.hE, by rw [x₁₂ sElen (by decide)]; exact hm.hL, hm.el, hm.L1,
    show p.len < 2 ^ 31 by omega, hm.e.congrK i₁₂ (k.trans k')⟩

/-- After the exponentiation. -/
def MC (p : MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64) (t₁ t₂ : State),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t₁.mem ∧
    Keep mmRegs σ t₁ ∧ Frm p.B (r2Ranges p.w) t₁.mem t₂.mem ∧ Keep mmRegs t₁ t₂ ∧
    Good t p.B p.Z p.w mi ∧ Frm p.B (expPhaseRanges p.w) t₂.mem t.mem ∧ Keep mmRegs t₂ t

/-- The exponentiation leaks the same in runs that agree on `n` and `e`. -/
theorem mainC_ct : RelCT isa (Two MB) (seqs expSteps) (Two MC) := by
  refine two_post (expPhase_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
  · obtain ⟨σ₁, xb₁, mi₁, u₁, hm₁, hv, so₁, f₁, k₁, hg₁, hlt₁, hr₁, f₁', k₁'⟩ := h₁
    obtain ⟨σ₂, xb₂, mi₂, u₂, hm₂, -, so₂, f₂, k₂, hg₂, hlt₂, hr₂, f₂', k₂'⟩ := h₂
    obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
    have := hm₁.k1
    obtain rfl := so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
    exact ⟨_, mb_ePre hm₁ hv so₁ f₁ k₁ hg₁ hlt₁ hr₁ f₁' k₁', mb_ePre hm₂ hv so₂ f₂ k₂ hg₂ hlt₂ hr₂ f₂' k₂'⟩
  rintro p t ⟨σ, xb, mi, t₁, hm, hv, so, f, k, hg, hlt, hr, f', k'⟩
  obtain ⟨X, hg', hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone, hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩ :=
    mb_ePre hm hv so f k hg hlt hr f' k'
  exact WP.mono (expPhase_ok hg' hZ hw hw' hodd hN1 hn hinv hX hone hlt2 hr2 he hlen hL hL1 hL' heb)
    fun t' ⟨hg'', _, f'', k''⟩ => ⟨σ, xb, mi, t₁, t, hm, hv, so, f, k, f', k', hg'', f'', k''⟩

/-- What the result's store needs, from the facts after the exponentiation. -/
theorem mc_oPre {p : MPub} {t σ t₁ t₂ : State} {xb : List Byte} {mi : BitVec 64}
    (hm : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (so : SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) (f : Frm p.B (setupRanges p.w) σ.mem t₁.mem)
    (k : Keep mmRegs σ t₁) (f' : Frm p.B (r2Ranges p.w) t₁.mem t₂.mem) (k' : Keep mmRegs t₁ t₂)
    (hg : Good t p.B p.Z p.w mi) (f'' : Frm p.B (expPhaseRanges p.w) t₂.mem t.mem) (k'' : Keep mmRegs t₂ t) :
    OPre ⟨⟨p.B, p.Z, p.w, mi⟩, p.k, p.op⟩ t := by
  have := hm.k1
  have := hm.k2
  have hZ : slot p.w 8 ≤ p.Z := hm.z
  have x := ((Fixed.of_frm f (setupRanges_fixed _)).trans (Fixed.of_frm f' (r2Ranges_fixed _))).trans
    (Fixed.of_frm f'' (expPhaseRanges_fixed _))
  have kk := (k.trans k').trans k''
  refine ⟨decide (Spec.Rsa.os2ip xb < p.N), hg, rfl, hZ, show 1 ≤ p.k by omega, show p.k < 2 ^ 31 by omega,
    by rw [x sOut (by decide)]; exact hm.hO, by rw [x sK (by decide)]; exact hm.hK, ?_,
    fun j hj => by rw [kk.2.2]; exact hm.out j hj, hm.outSep⟩
  rw [f''.ep_hdr (by decide) (by decide) (by decide) (by decide),
    f'.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold sMask sFn; omega)]
  exact so.mask

/-- `main` leaks the same in runs that agree on the public data, `n` and `e`. -/
theorem main_ct : RelCT isa (Two MRel) main fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp [r2Steps]) (RelCT.seq mainA_ct ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [expSteps]) (RelCT.seq mainB_ct ?_)
  refine RelCT.seqs_append (by simp [expSteps]) (by simp [outSteps]) (RelCT.seq mainC_ct ?_)
  refine out_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h
  obtain ⟨σ₁, xb₁, mi₁, u₁, v₁, hm₁, hv, so₁, f₁, k₁, f₁', k₁', hg₁, f₁'', k₁''⟩ := h₁
  obtain ⟨σ₂, xb₂, mi₂, u₂, v₂, hm₂, -, so₂, f₂, k₂, f₂', k₂', hg₂, f₂'', k₂''⟩ := h₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
  have := hm₁.k1
  obtain rfl := so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
  exact ⟨_, mc_oPre hm₁ so₁ f₁ k₁ f₁' k₁' hg₁ f₁'' k₁'', mc_oPre hm₂ so₂ f₂ k₂ f₂' k₂' hg₂ f₂'' k₂''⟩

/-! ## The whole function -/

theorem WP.and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- The public data of `vg_rsa_public`: `main`'s and the stack pointer. -/
structure CPub where
  m : MPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CRel (p : CPub) (s : State) : Prop :=
  pubContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.m.B ∧ (stackArg s 3).toNat * 8 = p.m.Z ∧
    (s.gpr .rcx).toNat = p.m.k ∧ s.gpr .rdi = p.m.op ∧ s.gpr .rdx = p.m.np ∧ s.gpr .r8 = p.m.ep ∧
    stackArg s 0 = p.m.ip ∧ (s.gpr .r9).toNat = p.m.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.m.nb ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = p.m.eb

theorem entry_split : entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) := rfl

/-- After `entry`'s first instruction. -/
def C1 (p : CPub) (t : State) : Prop :=
  ∃ s, CRel p s ∧ t.gpr .r11 = p.m.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))])) t (HeadPost s)

/-- After `entry` and the reloads. -/
def C2 (p : CPub) (t : State) : Prop := ∃ s, CRel p s ∧ HeadPost s t

/-- After the modulus' check. -/
def C3 (p : CPub) (t : State) : Prop :=
  ∃ s t₁, CRel p s ∧ HeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.m.nb) p.m.k)

/-- `vg_rsa_public` leaks the same in runs that agree on the public data. -/
theorem code_ct : RelCT isa (Two CRel) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two C3) (RelCT.block_append (RelCT.seq (R := Two C2) ?_ ?_)) ?_
  · rw [entry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := codeCtx_of hs.1
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 24 })] ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (HeadPost s) := by
      rw [← entry_split]; exact head_ok c
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.1, c₂.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := codeCtx_of hs.1
    have hnb := c.hnb.congrK h.inScr h.keep
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2.2.2.2.2.2.2.2.2.2.1, ← hs.2.2.2.2.1]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    have pin : ∀ p t, (C3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.m.B :=
      fun p t ⟨⟨s, t₁, hs, h, _, k, _⟩, _⟩ => ((k.gpr (by decide)).trans h.rdi).trans hs.2.2.1
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rsi = p.m.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.m.k ∧
        t.gpr .rdi = p.m.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨⟨s, t₁, hs, h, hm, k, -⟩, -⟩
    have c := codeCtx_of hs.1
    have hpre := mainPre_of c h hm k
    have hn := hpre.scr.nowrap
    have := c.hZ
    have := c.hk1
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * i)) 8 := fun i hi =>
      hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
        t'.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨by rw [hsi, hs.2.2.2.2.2.1], by rw [hcx, hs.2.2.2.2.1],
        ((k'.gpr (by decide)).trans hpre.rdi).trans hs.2.2.1⟩
  · -- `main`.
    have toM : ∀ p t, C3 p t ∧ isa.eval .ne t = some false → MRel p.m t := by
      rintro p t ⟨⟨s, t₁, hs, h, hm, k, hz⟩, he⟩
      have c := codeCtx_of hs.1
      obtain ⟨_, -, hB, hZ, hk, hop, hnp, hep, hip, hlen, hnb, heb⟩ := hs
      have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.m.nb) p.m.k = true := by
        simp only [eval, hz] at he; simpa using he
      refine ⟨Spec.Rsa.bytesAt s.mem p.m.ip p.m.k, ?_, hv⟩
      have := mainPre_of c h hm k
      rw [hnb, heb, hB, hZ, hk, hop, hnp, hep, hip, hlen] at this
      exact this
    exact main_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h)
      fun _ _ h => h

/-- The public data of a state. -/
def cpubOf (s : State) : CPub :=
  ⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r8, stackArg s 0,
    (s.gpr .r9).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat⟩, s.gpr .rsp⟩

/-- `vg_rsa_public` is constant time but for `n` and `e`. -/
theorem code_constantTime : ConstantTime isa pubContract.pre pubContract.pub code := by
  refine RelCT.constantTime (code_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, -, a2, a3, hn, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rcx (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, hn.symm, he.symm⟩

end VG.Proof.Bignum.X86_64

