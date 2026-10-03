import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Rel

/-!
# ML-DSA signing on x86-64: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly` and `vg_mldsa_rej_ntt_poly4`, so they agree on `r15`
(`RA`), and leak the same (`expandA_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `r15`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  RR p D (fun σ s => IA p D σ e s) fun x y => x.gpr .r15 = y.gpr .r15

theorem callE_ok' {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (aBase p + e)), .ptr (sc oPS)]) s
      fun s' => JE p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3 _ (by decide)⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem sampleE_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (he : eChk p e = true) :
    RelCT isa (RA p D e) (sampleE P p e) (RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  rw [sampleE_eq]
  refine RelCT.seq (R := RR p D (fun σ s => IA p D σ e s ∧ bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e)
    fun x y => x.gpr .r15 = y.gpr .r15) ?_ (RelCT.seq (R := RR p D (JE p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_)
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => blkE_ok he h)
      (block_tr (rs := [.rbx]) rfl fun x y h r hr => ?_) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.lrel fun _ _ h => h.st).regs (.rbx, scrLen p) (by simp [sgR, sgW])
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => callE_ok' hP he h.1 h.2)
      ((rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, seedE, seedE, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (andE_ok he h) (WP.mono (and15_ok s) fun _ h => h.1))
      (block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

/-! ## Four entries at a time -/

/-- Two runs in a group, after the seeds of its first `j` entries, with the same `r15`. -/
abbrev RG (p : Params) (D e j : Nat) : State → State → Prop :=
  RR p D (fun σ s => GS p D σ e j s) fun x y => x.gpr .r15 = y.gpr .r15

theorem slot_tr {p : Params} {D e j : Nat} (hj4 : j < 4) (hc : slotChk p e j = true) :
    RelCT isa (RG p D e j) (.block (setSR p e j)) (RG p D e (j + 1)) :=
  stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => slot_ok hj4 hc h)
    (block_tr (rs := [.rbx]) rfl fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.lrel fun _ _ h => h.ia4.ia.st).regs (.rbx, scrLen p) (by simp [sgR, sgW]))
    fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]

theorem call4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (hc : callChk p e = true) :
    RelCT isa (RG p D e 4) (rej4At P (pS (aBase p + e)) (r4P p))
      (RR p D (fun σ s => IA4 p D σ (e + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  have hc' := hc
  simp only [callChk, Bool.and_eq_true] at hc'
  unfold rej4At
  refine RelCT.seq (R := RR p D (J4 p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => callG_ok hP hc h)
      ((rej4Call_tr hP hc'.2).mono (fun x y h => ⟨h.lrel fun _ _ h => h.ia4.ia.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, g₁, g₂⟩, _⟩ := h
    rw [g₁.seeds, g₂.seeds, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (and4_ok hc h) (WP.mono (and15_ok s) fun _ h => h.1))
      (block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

theorem sample4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat} (hc : g4Chk p (4 * g) = true) :
    RelCT isa (RR p D (fun σ s => IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (sample4 P p g)
      (RR p D (fun σ s => IA4 p D σ (4 * g + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  simp only [g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine RelCT.seq (RelCT.mono (slot_tr (by decide) s0) (fun x y h => RR.mono h
    (fun σ s h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) id) fun _ _ h => h) ?_
  refine RelCT.seq (slot_tr (by decide) s1) (RelCT.seq (slot_tr (by decide) s2) (RelCT.seq (slot_tr (by decide) s3) ?_))
  exact call4_tr hP cc

/-! ## The matrix -/

theorem cpR4_tr {p : Params} {D j : Nat} (hj : j < 4) (hc : cpChk p j = true) (hsk : 32 ≤ p.skLen) :
    RelCT isa (RR p D (fun σ s => ICopy p D σ j s) fun _ _ => True) (cpR4 j)
      (RR p D (fun σ s => ICopy p D σ (j + 1) s) fun _ _ => True) :=
  stepRR (F := fun _ _ => True) (fun σ s _ h => WP.mono (cpR4_ok hc hsk h) fun _ h => ⟨h, trivial⟩)
    (copy_tr (by decide) (by decide) (show oRS4 + 34 * j < 2 ^ 31 by simp only [oRS4]; omega) (by decide) (by decide)
      fun x y h => ⟨(h.lrel fun _ _ h => h.st).regs (.rbx, scrLen p) (by simp [sgR, sgW]),
        (h.lrel fun _ _ h => h.st).regs (.rbp, p.skLen) (by simp [sgR, sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) :
    RelCT isa (RR p D (fun σ s => St p D σ s ∧ s.gpr .r15 = 1) fun _ _ => True)
      (Impl.MlDsa.X86_64.Sign.expandA P p) (RA p D (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine RelCT.seq (R := RR p D (fun σ s => ICopy p D σ 0 s) fun _ _ => True) (stepRR (F := fun _ _ => True)
    (fun σ s _ h => WP.mono (copyRho_ok hcp hst hsk h.1) fun s1 ⟨S1, _, hb, e15⟩ =>
      ⟨⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h.2⟩, trivial⟩)
    (copy_tr (by decide) (by decide) (by decide) (by decide) (by decide) fun x y h =>
      ⟨(h.lrel fun _ _ h => h.1).regs (.rbx, scrLen p) (by simp [sgR, sgW]),
        (h.lrel fun _ _ h => h.1).regs (.rbp, p.skLen) (by simp [sgR, sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial) ?_
  have hC := seqR_tr (f := cpR4) (R := fun j => RR p D (fun σ s => ICopy p D σ j s) fun _ _ => True) 4 0
    fun j _ hj => cpR4_tr (by omega) (hc4 j (by omega)) hsk
  refine RelCT.seq (R := RR p D (fun σ s => ICopy p D σ 4 s) fun _ _ => True) hC ?_
  have hG := seqR_tr (f := sample4 P p)
    (R := fun g => RR p D (fun σ s => IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (p.k * p.ℓ / 4) 0
    fun g _ hg' => sample4_tr hP (hg g (by omega))
  rw [Nat.zero_add] at hG
  refine RelCT.seq (RelCT.mono hG (fun x y h => ?_) fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
    exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁.ia4, i₂.ia4⟩, i₁.r15.trans i₂.r15.symm⟩
  have hE := seqR_tr (f := sampleE P p) (R := fun k => RA p D k) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    fun k h1 hk => sampleE_tr hP (he k (by omega))
  rw [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at hE
  exact RelCT.mono hE (fun x y h => RR.mono h (fun σ s h => h.ia) id) fun _ _ h => h

end VG.Proof.MlDsa.X86_64.Sign
