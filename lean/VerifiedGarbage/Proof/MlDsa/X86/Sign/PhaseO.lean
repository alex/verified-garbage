import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseL
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA signing on x86 (32-bit): the signature

Untrusted: everything here is checked by Lean. Once an iteration passed,
`sig` is `c̃` (`outCopy_piece`), the `BitPack` of `z` (`packZ_piece`), in
range by the check of its norm (`inRange_of_norm`), and `HintBitPack(h)`
(`hpack_piece`), whose 1s are at most `ω` by the check of their number, and
whose leakage, the hint, two runs whose checks pass agree on (`hint_list`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) :
    ∀ i < n, -((γ - 1 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem coeff_slot {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {i j : Nat} (hi : i < p.k) :
    coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) (256 * i + j) = coeffAt m (Buf.addr s₀ (pS (5 + i))) j := by
  have e : Buf.addr s₀ (pS (5 + i)) = Buf.addr s₀ (sc (oP 5) (1024 * p.k)) + BitVec.ofNat 64 (1024 * i) := by
    show Buf.addr s₀ (sc (oP (5 + i)) 1024) = _
    rw [show oP (5 + i) = oP 5 + 1024 * i by simp only [oP]; omega]
    exact addr_off hp (by ofs) (by ofs)
  simp only [coeffAt]
  rw [e, BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]

theorem hintAt_of {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {f : Nat → Vector Bool n}
    (h : HF s₀ m p.k f) : hintAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) p.k = (List.range p.k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  rw [Vector.getElem_ofFn, coeff_slot hp ps hi, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = ((List.range k).map fun j => hintOnes [f j]).sum := by
  simp only [hintOnes, List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- The coefficients of the hint, as the list `hbitsV` of its bits. -/
theorem hint_list {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {f : Nat → Vector Bool n}
    (h : HF s₀ m p.k f) :
    (List.range (256 * p.k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) i).toNat) =
      ((List.range p.k).map f).flatMap fun hi => hi.toList.map Bool.toNat := by
  suffices ∀ k ≤ p.k, (List.range (256 * k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) i).toNat) =
      ((List.range k).map f).flatMap fun hi => hi.toList.map Bool.toNat from this p.k (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 256 * (k + 1) = 256 * k + 256 by omega, List.range_add, List.map_append, ih (by omega),
      List.range_succ (n := k), List.map_append, List.flatMap_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    have e := (h k (by omega)).2 0 (by decide) j h₁
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
    simp only [List.getElem_map, List.getElem_range, Function.comp, Vector.getElem_toList, coeff_slot hp ps (by omega : k < p.k),
      e, getElem!_pos (f k) j h₁]
    cases (f k)[j] <;> rfl

/-! ## The signature -/

/-- The `BitPack` of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (s₀ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p s₀ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- Before the signature, the last iteration `U s₀` having passed; with the
first `r` polynomials of `z` packed after `c̃` in `sig`. -/
structure OS (p : Params) (F : PrimsOk P) (U : State → Nat) (r : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  fy : Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * U s₀))
  fh : HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * U s₀))
  run : Run p F (U s₀) s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true
  pass : passS p (U s₀) s₀
  sig : bytesAt s.mem (Buf.addr s₀ (bSig 0 (cLen p + zLen p * r))) (cLen p + zLen p * r) =
    CTv p s₀ (p.ℓ * U s₀) ++ zEnc p s₀ (p.ℓ * U s₀) r

/-- A write of `sig` keeps `z` and the hint. -/
theorem sigKeep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {m m' : Mem} {fz : Nat → Poly} {fh : Nat → Vector Bool n}
    (hz : Fam s₀ m (yB p) p.ℓ fz) (hh : HF s₀ m p.k fh) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    (fr : Frame (FR s₀ bs N) m m') (hb : ∀ c ∈ bs, (Y p).ok c = true ∧ c.arg = 3) :
    Fam s₀ m' (yB p) p.ℓ fz ∧ HF s₀ m' p.k fh :=
  ⟨hz.keep hp ps hN fr (by simp only [nS, yB]; omega) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩,
    hh.keep hp ps hN fr (by simp only [nS]; omega) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩⟩

theorem sig_ok {o l : Nat} (h : o + l ≤ p.sigLen) (hl : 0 < l) : (Y p).okW (bSig o l) = true :=
  Lay.okW_iff.mpr ⟨Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 3 < 5), hl, by rw [Y_alen3]; exact h⟩, rfl⟩

/-- Before the signature, the last iteration `U s₀` having passed. -/
structure OI (p : Params) (F : PrimsOk P) (U : State → Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  fy : Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * U s₀))
  fh : HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * U s₀))
  run : Run p F (U s₀) s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true
  pass : passS p (U s₀) s₀
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * U s₀)

/-- `c̃` to `sig`. -/
theorem outCopy_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat) :
    SP p (OI p F U) (OS p F U 0) (copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4)) := by
  have hc := ps.hcLen
  have e4 : 4 * (cLen p / 4) = cLen p := by omega
  have e : copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4) =
      copyW SC ⟨SC, oCT, 4 * (cLen p / 4)⟩ ⟨3, 0, 4 * (cLen p / 4)⟩ (cLen p / 4) := rfl
  rw [e]
  refine copy_piece SC oCT 3 0 (cLen p / 4) (by omega) (by omega) (by ofs) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h c' fr hb => ?_
  have fr' : Frame (FR s₀ [⟨3, 0, 4 * (cLen p / 4)⟩] 80) s.mem s'.mem := fr.mono (by simp)
  have hk := sigKeep hp ps h.fy h.fh (by decide) fr' fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofs, rfl⟩
  refine ⟨c', hk.1, hk.2, h.run, h.ball, h.pass, ?_⟩
  rw [e4] at hb
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [show zEnc p s₀ (p.ℓ * U s₀) 0 = [] from rfl, List.append_nil]
  exact hb.trans h.ct

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
theorem packZ_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat) (r : Nat) (hr : r < p.ℓ) :
    SP p (OS p F U r) (OS p F U (r + 1)) (packZ P p r) := by
  have hz := ps.hzLen
  have hβ := ps.hβ
  have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have hc := ps.hcLen
  refine bp_piece F.bitPack (F.ok _ (by simp)) (p.γ₁ - 1) p.γ₁ (zLen p) ps.hz.1 ps.hz.2 ⟨by omega, by omega, by omega⟩
    SC (oP (yB p + r)) 3 (sigZ p r) (by ofs) (fun s₀ s _ h => ⟨h.ctx, (fam_at h.fy hr).1,
      inRange_of_norm (fam_at h.fy hr) (h.pass.1 r hr) (by omega)⟩) fun s₀ s s' hp h c' fr hb => ?_
  have hk := sigKeep hp ps h.fy h.fh (by decide) fr fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofs, rfl⟩
  refine ⟨c', hk.1, hk.2, h.run, h.ball, h.pass, ?_⟩
  rw [bytes_split hp s'.mem (o' := sigZ p r) (l₁ := cLen p + zLen p * r) (l₂ := zLen p) (by simp only [sigZ]; omega) (by rw [Nat.mul_succ]; omega)
    (by ofs) (by ofs), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide) (b := ⟨3, 0, cLen p + zLen p * r⟩) (by ofs) fr, h.sig, hb,
    (fam_at h.fy hr).2, List.append_assoc]
  simp only [zEnc, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The signature, of the last iteration `U s₀`. -/
abbrev sigV (p : Params) (s₀ : State) (κ : Nat) : List Byte :=
  CTv p s₀ κ ++ zEnc p s₀ κ p.ℓ ++ hintBitPack p.ω p.k ((List.range p.k).map (Hv p s₀ κ))

/-- `HintBitPack(h)` to `sig`. -/
theorem hpack_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → U s₀ = U s₀') :
    SP p (OS p F U p.ℓ) (fun s₀ s => Ctx (Y p) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * U s₀))
      (hintBitPackAt P (sc (oP 5) (1024 * p.k)) p.ω (bSig (sigH p) (p.ω + p.k))) := by
  have hz := ps.hzLen
  have hc := ps.hcLen
  have hsl := ps.hsigLen
  unfold hintBitPackAt
  rw [show (sc (oP 5) (1024 * p.k)).len / 4 = 256 * p.k by show 1024 * p.k / 4 = _; omega]
  refine hbp_piece F.hintBitPack (F.ok _ (by simp)) p.ω p.k ps.hhint SC (oP 5) 3 (sigH p) (by ofs)
    (fun s₀ s hp h => ⟨h.ctx, ?_⟩) (fun s₀ s₀' s s' hp hp' hq h h' => ?_) fun s₀ s s' hp h c' fr hb => ⟨c', ?_⟩
  · rw [hintAt_of hp ps h.fh, hintOnes_map]; exact h.pass.2.2.2
  · rw [hint_list hp ps h.fh, hint_list hp' ps h'.fh, ← hU s₀ s₀' hp hp' hq]
    exact (((run_at ps hq h.run).2 h.ball).2 h.pass)
  · rw [bytes_split hp s'.mem (o' := sigH p) (l₁ := cLen p + zLen p * p.ℓ) (l₂ := p.ω + p.k) (by simp only [sigH]; omega)
      (by omega) (by ofs) (by ofs), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide)
      (b := ⟨3, 0, cLen p + zLen p * p.ℓ⟩) (by ofs) fr, h.sig, hb, hintAt_of hp ps h.fh]

/-- The signature. -/
theorem output_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → U s₀ = U s₀') :
    SP p (OI p F U) (fun s₀ s => Ctx (Y p) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * U s₀)) (output P p) := by
  unfold output
  refine (outCopy_piece F ps U).seq (Piece.seq ?_ (hpack_piece F ps U hU))
  have := seqR_piece (p := p) (I := OS p F U) 0 p.ℓ fun r _ hr => packZ_piece F ps U r (by omega)
  simpa using this

end VG.Proof.MlDsa.X86.Sign
