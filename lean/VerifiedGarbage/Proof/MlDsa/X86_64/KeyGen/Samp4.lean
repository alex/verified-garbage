import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp

/-!
# ML-DSA key generation on x86-64: four entries of `Â` at a time

`expA4 g` sets the indices of entries `4g, …, 4g + 3` of `Â` in the four seeds
at `oSA4` (`slot_piece`), samples the four polynomials with one call of
`vg_mldsa_rej_ntt_poly4`, and masks them with its result (`call_piece`): it
takes `KSamp (4g)` to `KSamp (4g + 4)` (`expA4_piece`), and `expAll`, the
groups and then the last `kℓ mod 4` entries one at a time, takes `K1` to
`KSamp (kℓ)` (`sampAll_piece`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly coeffAt polyAt Reduced PolyIs poly4 seed4 minBounds)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seeds -/

/-- After the first `e` entries of `Â`, with the seeds of entries `e, …, e + j - 1` at `oSA4`. -/
structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : KSamp p σ e 0 s
  done : ∀ k < j, bytesAt s.mem (pa s (sc (oSA4 + 34 * k))) 34 = seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)

theorem slot_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {e j : Nat} (he : e + 4 ≤ p.k * p.ℓ)
    (hj : j < 4) {s : State} (h : GS p σ e j s) : WP isa (.block (setSR p e j)) s (GS p σ e (j + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.ks.k1.kc.lay hF hp
  have hq : (e + j) / p.ℓ < 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hr : (e + j) % p.ℓ < 256 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  unfold setSR
  refine WP.mono (setTwo_ok L (o := oSA4 + 34 * j + 32) hr hq (by lay) (by lay) (by lay))
    fun s' ⟨hP, hx, hb⟩ => ⟨h.ks.keep hF hp hP.b hx (by layk) (fun e' he' => by layk)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (hP.cs .r15 (by decide)), fun k hk => ?_⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP.b (by layk)]; exact h.done k hk'
  · rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, L.keepBytes hP.b (by layk), h.ks.k1.sa4 k hj,
      show pa s' (sc (oSA4 + 34 * k)) + BitVec.ofNat 64 32 = pa s' (sc (oSA4 + 34 * k + 32)) from off_add _ _ _,
      hP.pa rbx_cs, hb, seedA_eq]

theorem slot_piece {p : Params} (hF : PFacts p) {e j : Nat} (he : e + 4 ≤ p.k * p.ℓ) (hj : j < 4) :
    Piece p (GS p · e j) (GS p · e (j + 1)) (.block (setSR p e j)) :=
  ⟨fun _ _ hp h => slot_ok hF hp he hj h,
    rel_of (Q := Two p) (taintRel [.rbx] (fun x y h => two_rbx h) (hc := .block []) (by with_unfolding_all rfl))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.ks.k1.kc h₂.ks.k1.kc⟩

theorem seed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oSA4)) k = seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4) + BitVec.ofNat 64 (34 * k) = pa s (sc (oSA4 + 34 * k)) from off_add _ _ _]
  exact h.done k hk

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds are those of the entries, from `ρ`. -/
theorem GS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 4 s) :
    bytesAt s.mem (pa s (sc oSA4)) 136 = seedA (rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      seedA (rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ seedA (rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      seedA (rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (pa s (sc oSA4) + BitVec.ofNat 64 (34 * k)) 34 =
      seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := fun k hk => seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, add_ofNat_zero] at b0
  rw [bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-! ## The four polynomials -/

theorem coeffAt_poly4 (m : Mem) (a : Addr) (k j : Nat) : coeffAt m (poly4 a k) j = coeffAt m a (256 * k + j) := by
  unfold coeffAt poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega]

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (aP e)) k = pa s (aP (e + k)) := by
  unfold poly4
  rw [show pa s (aP e) + BitVec.ofNat 64 (1024 * k) = pa s (sc (oP e + 1024 * k)) from off_add _ _ _,
    show oP e + 1024 * k = oP (e + k) by simp only [oP]; omega]

/-- One bound for the four polynomials. -/
theorem bound4 {ρ : Nat → List Byte} {x : Nat → Poly} (h : ∀ k < 4, ∃ b : Spec.MlDsa.Bounds,
    rejNTTPoly b.rejNTT (ρ k) = some (x k)) : ∃ n : Nat, ∀ k < 4, rejNTTPoly n (ρ k) = some (x k) := by
  obtain ⟨b0, h0⟩ := h 0 (by decide)
  obtain ⟨b1, h1⟩ := h 1 (by decide)
  obtain ⟨b2, h2⟩ := h 2 (by decide)
  obtain ⟨b3, h3⟩ := h 3 (by decide)
  refine ⟨max (max b0.rejNTT b1.rejNTT) (max b2.rejNTT b3.rejNTT), fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h1
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h2
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h3

theorem call_ok {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ)
    {g : Nat} (hg : 4 * g + 4 ≤ p.k * p.ℓ) {s : State} (h : GS p σ (4 * g) 4 s) :
    WP isa (.seq (rej4At P.rej4 P.sfx (aP (4 * g)) (sc (oR4 p))) (mask (aP (4 * g)) 1024)) s
      (KSamp p σ (4 * g + 4) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S := h.ks.k1.kc.site hF hp
  have L := S.lay
  refine WP.seq (WP.mono (rej4At_ok (a := aP (4 * g)) (w := sc (oR4 p)) (sc_ok _ (by simp only [oP]; omega))
    (sc_ok _ (by simp only [oR4, oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rej4 S)
    fun s₂ ⟨hP₂, hx₂, hred, hout⟩ => ?_)
  have hP₂' : PPostB s s₂ [(aP (4 * g), 4096), (sc (oR4 p), 8192)] := hP₂.b
  have L₂ := L.post hP₂' (kgB_bases p)
  have hr01 : (s₂.gpr .rax).setWidth 32 = 0 ∨ (s₂.gpr .rax).setWidth 32 = 1 := by
    rcases hout with ⟨h1, _⟩ | ⟨h0, _⟩
    exacts [.inr h1, .inl h0]
  refine WP.mono (maskN_ok L₂ (a := aP (4 * g)) (N := 1024) (sc_ok _ (by simp only [oP]; omega))
    (show Reg.rbx ≠ .r15 by decide) (by decide) (by decide) (by lay) hr01) fun s₃ ⟨hP₃, hx₃, h15, hco⟩ => ?_
  have hP₃' : PPostB s₂ s₃ [(aP (4 * g), 4 * 1024)] := hP₃
  have hP₁₃ := PPostB.app hP₂' hP₃' (sc1_bases _ _)
  have e₂ : pa s₂ (aP (4 * g)) = pa s (aP (4 * g)) := hP₂'.pa rbx_bases
  rw [e₂] at hco
  have hco4 : ∀ k < 4, ∀ i < 256, coeffAt s₃.mem (poly4 (pa s (aP (4 * g))) k) i =
      if (s₂.gpr .rax).setWidth 32 = 1 then coeffAt s₂.mem (poly4 (pa s (aP (4 * g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4, coeffAt_poly4]; exact hco _ (by omega)
  -- Entry `4g + k` is polynomial `k` from `aP (4g)`.
  have e₃ : ∀ k, pa s₃ (aP (4 * g + k)) = poly4 (pa s (aP (4 * g))) k := fun k => by
    rw [pa_poly4]; exact hP₁₃.pa rbx_bases
  obtain ⟨A, S', hA, _, hG⟩ := h.ks.ex
  have h15₂ : s₂.gpr .r15 = s.gpr .r15 := hP₂.cs .r15 (by decide)
  rw [h15₂, r15_and (good_01 hG) hr01] at h15
  have ka : k1Chk p [(aP (4 * g), 4096)] = true := k1Chk_rbx (by simp only [oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [scrLen, Spec.MlDsa.scratchWords, oP]; omega)
  have kr : k1Chk p [(sc (oR4 p), 8192)] = true := k1Chk_rbx (by simp only [oR4, oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [scrLen, Spec.MlDsa.scratchWords, oR4, oP]; omega)
  refine ⟨h.ks.k1.step hF hp hP₁₃ (hx₃.trans hx₂) (k1Chk_append (ws₁ := [_, _]) (k1Chk_append (ws₁ := [_]) ka kr) ka),
    fun e' => if e' < 4 * g then A e'
    else polyAt s₃.mem (pa s₃ (aP e')), S', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    by_cases hlt : e' < 4 * g
    · rw [ifp hlt]
      exact polyIs_frame' L hP₁₃ (by layk) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, e' = 4 * g + k := ⟨e' - 4 * g, by omega⟩
      rw [e₃]
      by_cases h1 : (s₂.gpr .rax).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega))).2 (hred h1 k (by omega))
      · exact (masked_zero h1 (hco4 k (by omega))).1
  · rw [h15]
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, hb4⟩ | ⟨ho, k, hk, hn⟩
      · obtain ⟨n, hn⟩ := bound4 hb4
        refine .inl ⟨by rw [ifp ⟨h1, ho⟩], { b with rejNTT := max b.rejNTT n }, fun e' he' => ?_,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        by_cases hlt : e' < 4 * g
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k, rfl⟩ : ∃ k, e' = 4 * g + k := ⟨e' - 4 * g, by omega⟩
          have hk : k < 4 := by omega
          rw [e₃, (masked_one ho (hco4 k hk)).1, ← seed4_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [seed4_eq h hk] at hn
        have hq : (4 * g + k) / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega)
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega)) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

theorem call_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {g : Nat}
    (hg : 4 * g + 4 ≤ p.k * p.ℓ) :
    Piece p (GS p · (4 * g) 4) (KSamp p · (4 * g + 4) 0)
      (.seq (rej4At P.rej4 P.sfx (aP (4 * g)) (sc (oR4 p))) (mask (aP (4 * g)) 1024)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp h => call_ok hP hF hp hg h, rel_of (Q := fun x y => Two p x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_two hF p₁ p₂ pub h₁.ks.k1.kc h₂.ks.k1.kc,
      by rw [h₁.seeds, h₂.seeds, rho_pub pub]⟩⟩
  have ok := fun x (S : Site p x) => WP.mono (rej4At_ok (a := aP (4 * g)) (w := sc (oR4 p)) (sfx := P.sfx)
    (sc_ok _ (by simp only [oP]; omega)) (sc_ok _ (by simp only [oR4, oP]; omega)) (by lay) (by lay) (by lay)
    (by lay) (by lay) hP.rej4 S) fun _ h => (⟨_, h.1.b⟩ : ∃ W, PostB x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rej4At_tr (sfx := P.sfx) (sc_ok _ (by simp only [oP]; omega))
      (sc_ok _ (by simp only [oR4, oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rej4
      (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide))
      fun x y h => ⟨ok x h.1.sx, ok y h.1.sy⟩)
    (mask4_tr (j := 4 * g) (by omega) fun x y h => h.regs .rbx (by decide))

/-! ## The pieces -/

theorem expA4_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {g : Nat}
    (hg : 4 * g + 4 ≤ p.k * p.ℓ) :
    Piece p (KSamp p · (4 * g) 0) (KSamp p · (4 * g + 4) 0) (expA4 P p g) := by
  unfold expA4
  exact Piece.mono ((slot_piece hF hg (j := 0) (by decide)).seq ((slot_piece hF hg (j := 1) (by decide)).seq
    ((slot_piece hF hg (j := 2) (by decide)).seq ((slot_piece hF hg (j := 3) (by decide)).seq (call_piece hP hF hg)))))
    (fun _ _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ _ _ h => h

/-- The entries of `Â`. -/
theorem sampAll_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => K1 p σ s ∧ s.gpr .r15 = 1) (fun σ s => KSamp p σ (p.k * p.ℓ) 0 s) (expAll P p) := by
  unfold expAll
  refine Piece.seq (J := fun σ s => KSamp p σ (4 * (p.k * p.ℓ / 4)) 0 s) ?_ ?_
  · refine Piece.mono (Piece.seqR (I := fun g σ s => KSamp p σ (4 * g) 0 s) (p.k * p.ℓ / 4) 0
      fun g _ hg => Piece.mono (expA4_piece hP hF (g := g) (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_)
      (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
    · rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact h
    · simpa using h
  · refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p σ e 0 s) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
      fun e h1 h2 => expA_piece hP hF (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
    rwa [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at h

end VG.Proof.MlDsa.X86_64.KeyGen
