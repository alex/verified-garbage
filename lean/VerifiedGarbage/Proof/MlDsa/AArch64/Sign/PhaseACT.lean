import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel

/-!
# ML-DSA signing on AArch64: `ExpandA` leaks only `ρ`

Untrusted: everything here is checked by Lean. Two runs of `ExpandA` with
the same `ρ` compute the same results of `vg_mldsa_rej_ntt_poly`, so they
agree on `x24` (`RA`), and leak the same (`expandA_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `x24`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  RR p D (fun σ s => IA p D σ e s) fun x y => x.gpr .x24 = y.gpr .x24

theorem callE_ok' {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (aBase p + e))),
      (.x2, .ptr (sc oPS))]) s fun s' => JE p D e σ s' ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem blkE_taint (p : Params) (e : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (blkE p e)) (.block [])).isSome = true := by
  dsimp only [blkE, setB]; rfl

theorem sampleE_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (he : eChk p e = true) :
    RelCT isa (RA p D e) (sampleE P p e) (RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  rw [sampleE_eq]
  refine RelCT.seq (R := RR p D (fun σ s => IA p D σ e s ∧ bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e)
    fun x y => x.gpr .x24 = y.gpr .x24) ?_ (RelCT.seq (R := RR p D (JE p D e)
      fun x y => x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) ?_ ?_)
  · exact stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => blkE_ok he h)
      (lrel_tr (fun x y h => h.lrel fun _ _ h => h.st) (blkE_taint p e)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
  · refine stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => callE_ok' hP he h.1 h.2)
      ((rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, seedE, seedE, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .x24 =
        BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
      (fun σ s _ h => WP.conj (andE_ok he h) (WP.mono (and24_ok s) fun _ h => h.2))
      (lrel_tr (fun x y h => h.lrel fun _ σ h => ?_) (by taint_decide)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]
    obtain ⟨s₀, h₀, hP₀, -⟩ := h
    exact h₀.st.step hP₀ (eChk_spec he).2.2.1

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) :
    RelCT isa (RR p D (fun σ s => St p D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.expandA P p) (RA p D (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine RelCT.seq (R := RA p D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA p D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have := seqR_tr (f := sampleE P p) (R := fun k => RA p D k) (p.k * p.ℓ) 0
      fun k _ hk => sampleE_tr hP (he k (by omega))
    rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.AArch64.Sign
