import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseL

/-!
# ML-DSA signing on x86-64: the signature

Untrusted: everything here is checked by Lean. Once an iteration passed:
`c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r` (in range, as `z`
passed its norm check: `inRange_of_norm`), then `HintBitPack(h)` (with at
most `ω` 1s) to `sig`, which then holds `sigEncode(c̃, z mod± q, h)`
(`output_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [VG.Proof.MlKem.X86_64.off_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    pa s (pS (5 + i)) = pa s (Impl.MlDsa.X86_64.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show s.gpr .rbx + BitVec.ofNat 64 (oP (5 + i)) = s.gpr .rbx + BitVec.ofNat 64 (oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [VG.Proof.MlKem.X86_64.off_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega]

theorem r14_bases (o : Nat) : ((.r14, o) : Ptr).1 ∈ bases := by
  show Reg.r14 ∈ bases; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : IK p D σ s
  z : Fam s (yBase p) p.ℓ (Zv p σ κ)
  h : HFam s 5 p.k (Hv p σ κ)
  sig : bytesAt s.mem (pa s (.r14, 0)) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r
  r15 : s.gpr .r15 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && famChk (sgB p) ws (yBase p) p.ℓ && famChk (sgB p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : ofam p ws = true)
    (hs : keepB (sgB p) ws (.r14, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .r15 = s.gpr .r15) :
    OS p D σ κ r s' := by
  simp only [ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.r15⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  copyChk (sgB p) (sgW p) (.r14, 0) (sc oCT) (cLen p) && ofam p [((.r14, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (sgB p) (sgW p) (yP p r) 1024 (.r14, sigZ p r) (zLen p) &&
      ofam p [((.r14, sigZ p r), zLen p)] && keepB (sgB p) [((.r14, sigZ p r), zLen p)] (.r14, 0) (cLen p + zLen p * r)) &&
    rwChk (sgB p) (sgW p) (hP 0) (256 * p.k * 4) (.r14, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    ikChk p [((.r14, sigH p), p.ω + p.k)] &&
    keepB (sgB p) [((.r14, sigH p), p.ω + p.k)] (.r14, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : Ok3 p) : oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

theorem output_ok {P : Prims} {D : Nat} (hPO : PrimsOk P D) {p : Params} (hc : oChk p = true) {σ : State} {κ : Nat}
    {s : State} (hk : IK p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (hpass : PassV p σ κ)
    (h15 : s.gpr .r15 = 1) :
    WP isa (output P p) s fun s' => IK p D σ s' ∧ bytesAt s'.mem (pa s' (.r14, 0)) p.sigLen = sigV p σ κ ∧
      s'.gpr .r15 = 1 := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L := hk.d.im.st.lay
  unfold output
  refine WP.seq (WP.mono (copy_okB L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_)
  have O0 : OS p D σ κ 0 s1 := by
    simp only [ofam, Bool.and_eq_true] at c0
    refine ⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
      by rw [hcs1 _ (by decide), h15]⟩
    rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
    simp [zEnc]
  refine WP.seq (WP.mono (seqR_ok (I := fun r => OS p D σ κ r) p.ℓ 0 (fun r _ hr s h => ?_) s1 O0) fun s2 h2 => ?_)
  · obtain ⟨⟨c1, c2⟩, c3⟩ := cz r (by omega)
    have Lh := h.k.d.im.st.lay
    have hzr := h.z r (by omega)
    refine WP.mono (bpAt_ok hPO Lh hbp hzl c1 hzr.1 (inRange_of_norm hzr (hpass.1 r (by omega)) (Nat.sub_le _ _)))
      fun s' ⟨hP', hcs', hb'⟩ => ?_
    have O' := h.step hP' c2 c3 (hcs' _ (by decide))
    refine ⟨O'.k, O'.z, O'.h, ?_, O'.r15⟩
    rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, pa_add, Nat.zero_add,
      hP'.pa (r14_bases _), hb', hzr.2, zEnc, zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.append_assoc]
  rw [Nat.zero_add] at h2
  have L2 := h2.k.d.im.st.lay
  have hones : hintOnes (hintAt s2.mem (pa s2 (hP 0)) p.k) ≤ p.ω := by
    rw [hintAt_of (f := Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [pS_hint] at this,
      hintOnes_map]
    exact hpass.2.2.2
  refine WP.mono (hbpAt_ok hPO L2 hhp ch hones) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3 _ (by decide), h2.r15]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, hintAt_of (f := Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [pS_hint] at this]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

end VG.Proof.MlDsa.X86_64.Sign
