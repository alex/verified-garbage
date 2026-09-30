import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageZ

/-!
# ML-DSA verification on x86-64: the samplers

Untrusted: everything here is checked by Lean. `ρ` to `SB`; each entry
`Â[r, s]` sampled from `ρ ‖ s ‖ r` (`aOne_ok`), and `c` (`ball_ok`), each
reduced, and `r15` 1 only if every sampler succeeded, with their outputs
(`S3`, `S4`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed)

/-! ## The seed -/

theorem seed_bytes (m : Mem) (A : Addr) (b1 b2 : Byte) :
    bytesAt ((m.writeW (A + BitVec.ofNat 64 32) b1).writeW (A + BitVec.ofNat 64 33) b2) A 34 =
      bytesAt m A 32 ++ [b1] ++ [b2] := by
  refine Proof.MlKem.bytesAt_eq (by simp [Proof.MlKem.bytesAt_length]) fun i hi => ?_
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
  rcases (by omega : i < 32 ∨ i = 32 ∨ i = 33) with h | rfl | rfl
  · have n1 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    have n2 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 32 := by intro e; bv_omega
    rw [ifn n1, ifn n2]
    simp [List.getElem_append_left, Proof.MlKem.bytesAt_getElem, h, Proof.MlKem.bytesAt_length]
  · have n1 : A + BitVec.ofNat 64 32 ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    rw [ifn n1, ifp rfl]
    simp [Proof.MlKem.bytesAt_length]
  · rw [ifp rfl]
    simp [Proof.MlKem.bytesAt_length]

theorem integerToBytes_one (x : Nat) : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]


/-! ## `Â` -/

/-- Entry `(r', c')` of `Â` is sampled before entry `(r, c)`. -/
def Done (r c r' c' : Nat) : Prop := r' < r ∨ (r' = r ∧ c' < c)

/-- After the entries of `Â` before `(r, c)`, with the hint `h`. -/
structure S3 (p : Params) (h : List (Vector Bool n)) (r c : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  rho : bytesAt st.mem (pa st (sc oSB)) 32 = vRho (vPk p σ)
  red : ∀ r' < p.k, ∀ c' < p.ℓ, Done r c r' c' → Reduced st.mem (pa st (pA r' c'))
  ok : ∃ q : Bool, st.gpr .r15 = flag (q = true) ∧
    (q = true → ∀ r' < p.k, ∀ c' < p.ℓ, Done r c r' c' →
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r' c') = some (polyAt st.mem (pa st (pA r' c')))) ∧
    (q = false → ∃ r' < p.k, ∃ c' < p.ℓ, Done r c r' c' ∧ rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r' c') = none)

abbrev wsB : List (Ptr × Nat) := [(sc (oSB + 32), 1), (sc (oSB + 33), 1)]
abbrev wsA (e : Nat) : List (Ptr × Nat) := [(pS (20 + e), 1024), (sc oSS, 2048)]

/-- A state keeps what `S3` says across a piece that writes `ws`. -/
def keepChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  tChk p ws && keepB (vB p) ws (pH 0) (1024 * p.k) && (List.range p.ℓ).all (fun i => keepB (vB p) ws (pZ i) 1024)

/-- The facts about the parameters entry `e = 8r + c` needs. -/
def aChk (p : Params) (e : Nat) : Bool :=
  inB (vW p) (sc (oSB + 32)) 1 && inB (vW p) (sc (oSB + 33)) 1 && rejChk (vB p) (vW p) (pS (20 + e)) &&
    inB (vB p) (pS (20 + e)) 1024 && inB (vW p) (pS (20 + e)) 1024 && keepChk p wsB && keepChk p (wsA e) &&
    keepB (vB p) wsB (sc oSB) 32 && keepB (vB p) (wsA e) (sc oSB) 32 &&
    (List.range p.k).all (fun r' => (List.range p.ℓ).all fun c' => !decide (8 * r' + c' < e) ||
      (keepB (vB p) wsB (pS (20 + 8 * r' + c')) 1024 && keepB (vB p) (wsA e) (pS (20 + 8 * r' + c')) 1024))

theorem aChk_all : ∀ p ∈ params, ∀ r < p.k, ∀ c < p.ℓ, aChk p (8 * r + c) = true := by decide


theorem keepChk_spec {p : Params} {ws : List (Ptr × Nat)} (h : keepChk p ws = true) :
    tChk p ws = true ∧ keepB (vB p) ws (pH 0) (1024 * p.k) = true ∧ ∀ i < p.ℓ, keepB (vB p) ws (pZ i) 1024 = true := by
  simp only [keepChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem setB2_ok {p : Params} {s : State} (L : Lay (vR p) (vW p) s) (h32 : inB (vW p) (sc (oSB + 32)) 1 = true)
    (h33 : inB (vW p) (sc (oSB + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (setB (sc (oSB + 32)) x ++ setB (sc (oSB + 33)) y)) s fun s' => PPostB s s' wsB ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (pa s (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (pa s (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) := by
  have e32 : pa s (sc (oSB + 32)) = pa s (sc oSB) + BitVec.ofNat 64 32 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e33 : pa s (sc (oSB + 33)) = pa s (sc oSB) + BitVec.ofNat 64 33 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok _ x (by decide) hx s (L.inW h32)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have e₁ : pa s₁ (sc (oSB + 33)) = pa s (sc (oSB + 33)) := by simp only [pa]; rw [k₁.gpr (by decide)]
  refine WP.mono (setB_ok _ y (by decide) hy s₁ (by rw [k₁.2.2, e₁]; exact L.inW h33)) fun s₂ ⟨hm₂, k₂⟩ =>
    ⟨postB_of_keep (k₁.trans k₂) (by decide) ?_, by rw [k₂.gpr (by decide), k₁.gpr (by decide)], ?_⟩
  · rw [hm₂, hm₁, e₁]
    have hc : ∀ q : Ptr, (Region.mk (pa s q) 1).Contains (pa s q) 1 := fun q => Region.contains_self _ _
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc _)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (hc _)
  · rw [hm₂, hm₁, e₁, e32, e33]


theorem kl_le : ∀ p ∈ params, p.ℓ ≤ 7 ∧ p.k ≤ 8 := by decide

theorem done_succ {r c r' c' : Nat} : Done r (c + 1) r' c' ↔ Done r c r' c' ∨ (r' = r ∧ c' = c) := by
  unfold Done; omega

theorem aOne_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) {s : State} (hs : S3 p h r c σ s) :
    WP isa (aOne P (8 * r + c)) s (S3 p h r (c + 1) σ) := by
  have hck := aChk_all p hp r hr c hc
  have hkl := kl_le p hp
  have hc8 : c < 8 := by omega
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h32, h33⟩, hrej⟩, hin⟩, hwa⟩, kB⟩, kA⟩, kSB⟩, kSA⟩, kE⟩ := hck
  obtain ⟨tB, hB, zB⟩ := keepChk_spec kB
  obtain ⟨tA, hA, zA⟩ := keepChk_spec kA
  have L := hs.t.lay hp hv
  have em : (8 * r + c) % 8 = c := by omega
  have ed : (8 * r + c) / 8 = r := by omega
  unfold aOne
  rw [em, ed]
  refine WP.seq (WP.mono (setB2_ok L h32 h33 c r (by omega) (by omega)) fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ tB
  have L₁ := t₁.lay hp hv
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSB)) 34 = aSeed (vPk p σ) r c := by
    rw [hP₁.pa (by decide), hm₁, seed_bytes, hs.rho, aSeed, integerToBytes_one, integerToBytes_one]
  obtain ⟨q, h15, hok, hbad⟩ := hs.ok
  refine WP.mono (sampled_ok L₁ hin hwa (h15₁.trans h15) (List.mem_cons_self ..)
    (WP.mono (rejNttAt_ok C.rejNtt L₁ hrej) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₂ ⟨hP₂, hred, rr, hrr, h15₂, hs1, hs0⟩ => ?_
  rw [hseed] at hs1 hs0
  have hPA : pa s₂ (pA r c) = pa s₁ (pS (20 + (8 * r + c))) := by
    rw [hP₂.pa (show Reg.rbx ∈ bases by decide), pA, show 20 + 8 * r + c = 20 + (8 * r + c) by omega]
  refine ⟨t₁.step hp hv hP₂ tA, L₁.keepHint hP₂ hA (L.keepHint hP₁ hB hs.hint),
    fun i hi => L₁.keepPoly hP₂ (zA i hi) (L.keepPoly hP₁ (zB i hi) (hs.z i hi)),
    by rw [L₁.keepBytes hP₂ kSA, L.keepBytes hP₁ kSB, hs.rho], fun r' hr' c' hc' hd => ?_,
    ⟨q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩⟩
  · rcases done_succ.mp hd with hd | ⟨rfl, rfl⟩
    · have := kE r' hr' c' hc'
      have hlt : 8 * r' + c' < 8 * r + c := by unfold Done at hd; omega
      rw [or_iff_right (by omega)] at this
      exact L₁.keepRed hP₂ this.2 (L.keepRed hP₁ this.1 (hs.red r' hr' c' hc' hd))
    · rw [hPA]; exact hred
  · rw [h15₂]
    exact flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rcases done_succ.mp hd with hd | ⟨rfl, rfl⟩
    · have := kE r' hr' c' hc'
      have hlt : 8 * r' + c' < 8 * r + c := by unfold Done at hd; omega
      rw [or_iff_right (by omega)] at this
      obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' hd
      exact ⟨b, by rw [hb, L₁.keepPolyAt hP₂ this.2, L.keepPolyAt hP₁ this.1]⟩
    · obtain ⟨b, hb⟩ := hs1 hq.2
      exact ⟨b, by rw [hb, hPA]⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', done_succ.mpr (.inl hd), hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact ⟨r, hr, c, hc, done_succ.mpr (.inr ⟨rfl, rfl⟩), hs0 h0⟩

end VG.Proof.MlDsa.X86_64.Verify
