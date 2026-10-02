import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageZ

/-!
# ML-DSA verification on x86-64: the samplers

`ρ` to `SB` and `SB4`; each entry `Â[r, s]` (number `ℓr + s`) sampled from
`ρ ‖ s ‖ r`, four at a time (`aGrp_ok`) and then one at a time (`aOne_ok`),
and `c` (`ballStage_ok`), each reduced, and `r15` 1 only if every sampler
succeeded, with their outputs (`S3`, `S4`).
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

/-- Entry `(r', c')` of `Â`, number `l r' + c'` in rows of `l` entries, is sampled before entry `e`. -/
def Done (l e r' c' : Nat) : Prop := l * r' + c' < e

theorem rc_eq {l r c e : Nat} (hc : c < l) (h : l * r + c = e) : r = e / l ∧ c = e % l := by
  have hl : 0 < l := by omega
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem pA_eq (l r c : Nat) : pA l r c = pS (20 + (l * r + c)) := by
  show pS (20 + l * r + c) = _
  rw [Nat.add_assoc]

theorem l_pos : ∀ p ∈ params, 0 < p.ℓ := by decide

/-- Entry `e < kℓ` is `Â[e / ℓ, e mod ℓ]`. -/
theorem entry_lt {p : Params} (hp : p ∈ params) {e : Nat} (he : e < p.k * p.ℓ) : e / p.ℓ < p.k ∧ e % p.ℓ < p.ℓ :=
  ⟨(Nat.div_lt_iff_lt_mul (l_pos p hp)).mpr he, Nat.mod_lt _ (l_pos p hp)⟩

theorem done_all {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : Done p.ℓ (p.k * p.ℓ) r c := by
  unfold Done
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- After the first `e` entries of `Â`, with the hint `h`. -/
structure S3 (p : Params) (h : List (Vector Bool n)) (e : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  rho : bytesAt st.mem (pa st (sc oSB)) 32 = vRho (vPk p σ)
  rho4 : ∀ k < 4, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 32 = vRho (vPk p σ)
  red : ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → Reduced st.mem (pa st (pA p.ℓ r' c'))
  ok : ∃ q : Bool, st.gpr .r15 = flag (q = true) ∧
    (q = true → ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' →
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r' c') = some (polyAt st.mem (pa st (pA p.ℓ r' c')))) ∧
    (q = false → ∃ r' < p.k, ∃ c' < p.ℓ, Done p.ℓ e r' c' ∧ rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r' c') = none)

abbrev wsB : List (Ptr × Nat) := [(sc (oSB + 32), 1), (sc (oSB + 33), 1)]
abbrev wsA (e : Nat) : List (Ptr × Nat) := [(pS (20 + e), 1024), (sc oSS, 2048)]

/-- A state keeps what `S3` says across a piece that writes `ws`. -/
def keepChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  tChk p ws && keepB (vB p) ws (pH 0) (1024 * p.k) && (List.range p.ℓ).all (fun i => keepB (vB p) ws (pZ i) 1024)

/-- The facts about the parameters entry `e` needs. -/
def aChk (p : Params) (e : Nat) : Bool :=
  inB (vW p) (sc (oSB + 32)) 1 && inB (vW p) (sc (oSB + 33)) 1 && rejChk (vB p) (vW p) (pS (20 + e)) &&
    inB (vB p) (pS (20 + e)) 1024 && inB (vW p) (pS (20 + e)) 1024 && keepChk p wsB && keepChk p (wsA e) &&
    keepB (vB p) wsB (sc oSB) 32 && keepB (vB p) (wsA e) (sc oSB) 32 &&
    (List.range p.k).all (fun r' => (List.range p.ℓ).all fun c' => !decide (p.ℓ * r' + c' < e) ||
      (keepB (vB p) wsB (pA p.ℓ r' c') 1024 && keepB (vB p) (wsA e) (pA p.ℓ r' c') 1024)) &&
    (List.range 4).all (fun k => keepB (vB p) wsB (sc (oSB4 + 34 * k)) 32 &&
      keepB (vB p) (wsA e) (sc (oSB4 + 34 * k)) 32)

theorem aChk_all : ∀ p ∈ params, ∀ e < p.k * p.ℓ, aChk p e = true := by decide


theorem keepChk_spec {p : Params} {ws : List (Ptr × Nat)} (h : keepChk p ws = true) :
    tChk p ws = true ∧ keepB (vB p) ws (pH 0) (1024 * p.k) = true ∧ ∀ i < p.ℓ, keepB (vB p) ws (pZ i) 1024 = true := by
  simp only [keepChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem setB2At_ok {p : Params} {s : State} (L : Lay (vR p) (vW p) s) (B : Nat)
    (h32 : inB (vW p) (sc (B + 32)) 1 = true)
    (h33 : inB (vW p) (sc (B + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (setB (sc (B + 32)) x ++ setB (sc (B + 33)) y)) s fun s' =>
      PPostB s s' [(sc (B + 32), 1), (sc (B + 33), 1)] ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (pa s (sc B) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (pa s (sc B) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) := by
  have e32 : pa s (sc (B + 32)) = pa s (sc B) + BitVec.ofNat 64 32 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e33 : pa s (sc (B + 33)) = pa s (sc B) + BitVec.ofNat 64 33 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok _ x (show Reg.rbx ≠ .rax by decide) hx s (L.inW h32)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have e₁ : pa s₁ (sc (B + 33)) = pa s (sc (B + 33)) := by simp only [pa]; rw [k₁.gpr (by decide)]
  refine WP.mono (setB_ok _ y (show Reg.rbx ≠ .rax by decide) hy s₁ (by rw [k₁.2.2, e₁]; exact L.inW h33)) fun s₂ ⟨hm₂, k₂⟩ =>
    ⟨postB_of_keep (k₁.trans k₂) (by decide) ?_, by rw [k₂.gpr (by decide), k₁.gpr (by decide)], ?_⟩
  · rw [hm₂, hm₁, e₁]
    have hc : ∀ q : Ptr, (Region.mk (pa s q) 1).Contains (pa s q) 1 := fun q => Region.contains_self _ _
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc _)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (hc _)
  · rw [hm₂, hm₁, e₁, e32, e33]

theorem setB2_ok {p : Params} {s : State} (L : Lay (vR p) (vW p) s) (h32 : inB (vW p) (sc (oSB + 32)) 1 = true)
    (h33 : inB (vW p) (sc (oSB + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (setB (sc (oSB + 32)) x ++ setB (sc (oSB + 33)) y)) s fun s' => PPostB s s' wsB ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (pa s (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (pa s (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) :=
  setB2At_ok L oSB h32 h33 x y hx hy

theorem kl_le : ∀ p ∈ params, p.ℓ ≤ 7 ∧ p.k ≤ 8 := by decide

theorem done_succ {l e r' c' : Nat} : Done l (e + 1) r' c' ↔ Done l e r' c' ∨ l * r' + c' = e := by
  unfold Done; omega

theorem aOne_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {e : Nat} (he : e < p.k * p.ℓ) {s : State} (hs : S3 p h e σ s) :
    WP isa (aOne P p e) s (S3 p h (e + 1) σ) := by
  have hck := aChk_all p hp e he
  have hkl := kl_le p hp
  obtain ⟨hr, hc⟩ := entry_lt hp he
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h32, h33⟩, hrej⟩, hin⟩, hwa⟩, kB⟩, kA⟩, kSB⟩, kSA⟩, kE⟩, k4⟩ := hck
  obtain ⟨tB, hB, zB⟩ := keepChk_spec kB
  obtain ⟨tA, hA, zA⟩ := keepChk_spec kA
  have L := hs.t.lay hp hv
  unfold aOne
  refine WP.seq (WP.mono (setB2_ok L h32 h33 (e % p.ℓ) (e / p.ℓ) (by omega) (by omega))
    fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ tB
  have L₁ := t₁.lay hp hv
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSB)) 34 = aSeed (vPk p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [hP₁.pa (by decide), hm₁, seed_bytes, hs.rho, aSeed, integerToBytes_one, integerToBytes_one]
  obtain ⟨q, h15, hok, hbad⟩ := hs.ok
  refine WP.mono (sampled_ok L₁ hin hwa (h15₁.trans h15) (List.mem_cons_self ..)
    (WP.mono (rejNttAt_ok C.rejNtt L₁ hrej) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₂ ⟨hP₂, hred, rr, hrr, h15₂, hs1, hs0⟩ => ?_
  rw [hseed] at hs1 hs0
  have hPA : ∀ r' c', c' < p.ℓ → p.ℓ * r' + c' = e →
      pa s₂ (pA p.ℓ r' c') = pa s₁ (pS (20 + e)) ∧ r' = e / p.ℓ ∧ c' = e % p.ℓ := fun r' c' hc' he' =>
    ⟨by rw [hP₂.pa (show Reg.rbx ∈ bases by decide), pA_eq, he'], rc_eq hc' he'⟩
  refine ⟨t₁.step hp hv hP₂ tA, L₁.keepHint hP₂ hA (L.keepHint hP₁ hB hs.hint),
    fun i hi => L₁.keepPoly hP₂ (zA i hi) (L.keepPoly hP₁ (zB i hi) (hs.z i hi)),
    by rw [L₁.keepBytes hP₂ kSA, L.keepBytes hP₁ kSB, hs.rho],
    fun k hk => by rw [L₁.keepBytes hP₂ (k4 k hk).2, L.keepBytes hP₁ (k4 k hk).1, hs.rho4 k hk],
    fun r' hr' c' hc' hd => ?_,
    ⟨q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩⟩
  · rcases done_succ.mp hd with hd | he'
    · have := kE r' hr' c' hc'
      rw [or_iff_right (by unfold Done at hd; omega)] at this
      exact L₁.keepRed hP₂ this.2 (L.keepRed hP₁ this.1 (hs.red r' hr' c' hc' hd))
    · rw [(hPA r' c' hc' he').1]; exact hred
  · rw [h15₂]
    exact flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rcases done_succ.mp hd with hd | he'
    · have := kE r' hr' c' hc'
      rw [or_iff_right (by unfold Done at hd; omega)] at this
      obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' hd
      exact ⟨b, by rw [hb, L₁.keepPolyAt hP₂ this.2, L.keepPolyAt hP₁ this.1]⟩
    · obtain ⟨e1, e2, e3⟩ := hPA r' c' hc' he'
      obtain ⟨b, hb⟩ := hs1 hq.2
      refine ⟨b, ?_⟩
      rw [e1, e2, e3]
      exact hb
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', done_succ.mpr (.inl hd), hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact ⟨e / p.ℓ, hr, e % p.ℓ, hc, done_succ.mpr (.inr (Nat.div_add_mod e p.ℓ)), hs0 h0⟩

/-! ## Four entries at a time -/

/-- A piece writing `ws` keeps the entries done before `e` but those `ex` says, and `S3`'s other facts. -/
def s3Chk (p : Params) (e : Nat) (ex : Nat → Nat → Bool) (ws : List (Ptr × Nat)) : Bool :=
  keepChk p ws && keepB (vB p) ws (sc oSB) 32 && (List.range 4).all (fun k => keepB (vB p) ws (sc (oSB4 + 34 * k)) 32) &&
    (List.range p.k).all (fun r' => (List.range p.ℓ).all fun c' =>
      !decide (p.ℓ * r' + c' < e) || ex r' c' || keepB (vB p) ws (pA p.ℓ r' c') 1024)

theorem s3Chk_spec {p : Params} {e : Nat} {ex : Nat → Nat → Bool} {ws : List (Ptr × Nat)}
    (h : s3Chk p e ex ws = true) :
    keepChk p ws = true ∧ keepB (vB p) ws (sc oSB) 32 = true ∧
      (∀ k < 4, keepB (vB p) ws (sc (oSB4 + 34 * k)) 32 = true) ∧
      ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → ex r' c' = false → keepB (vB p) ws (pA p.ℓ r' c') 1024 = true := by
  simp only [s3Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun k hk => List.all_eq_true.mp h3 k (List.mem_range.mpr hk), fun r' hr' c' hc' hd hx => ?_⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h4 r' (List.mem_range.mpr hr')) c' (List.mem_range.mpr hc')
  rw [decide_eq_true (show p.ℓ * r' + c' < e from hd), hx] at this
  simpa using this

/-- `S3` across a piece that writes `ws`, which `s3Chk` says keeps it. -/
theorem S3.keep {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)} {e : Nat}
    {s s' : State} (hs : S3 p h e σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hc : s3Chk p e (fun _ _ => false) ws = true) : S3 p h e σ s' := by
  obtain ⟨hk, kSB, k4, kE⟩ := s3Chk_spec hc
  obtain ⟨tk, hh, zk⟩ := keepChk_spec hk
  have L := hs.t.lay hp hv
  obtain ⟨q, hq, hok, hbad⟩ := hs.ok
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hh hs.hint, fun i hi => L.keepPoly hP (zk i hi) (hs.z i hi),
    by rw [L.keepBytes hP kSB, hs.rho], fun k hk => by rw [L.keepBytes hP (k4 k hk), hs.rho4 k hk],
    fun r' hr' c' hc' hd => L.keepRed hP (kE r' hr' c' hc' hd rfl) (hs.red r' hr' c' hc' hd),
    q, by rw [h15, hq], fun hq' r' hr' c' hc' hd => ?_, hbad⟩
  obtain ⟨b, hb⟩ := hok hq' r' hr' c' hc' hd
  exact ⟨b, by rw [hb, L.keepPolyAt hP (kE r' hr' c' hc' hd rfl)]⟩

/-- The two bytes of seed `j` of `SB4`. -/
abbrev wsS (j : Nat) : List (Ptr × Nat) := [(sc (oSB4 + 34 * j + 32), 1), (sc (oSB4 + 34 * j + 33), 1)]

/-- What setting the bytes of seed `j` needs, after `e` entries. -/
def slotChk (p : Params) (e j : Nat) : Bool :=
  inB (vW p) (sc (oSB4 + 34 * j + 32)) 1 && inB (vW p) (sc (oSB4 + 34 * j + 33)) 1 &&
    s3Chk p e (fun _ _ => false) (wsS j) &&
    (List.range j).all (fun k => keepB (vB p) (wsS j) (sc (oSB4 + 34 * k)) 34)

/-- After the bytes of the first `j` seeds of `SB4`, for the entries `e + k`. -/
structure GS (p : Params) (h : List (Vector Bool n)) (e j : Nat) (σ st : State) : Prop where
  s3 : S3 p h e σ st
  done : ∀ k < j, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 34 = aSeed (vPk p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)

theorem slot_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)}
    {e j : Nat} (hj : j < 4) (he : e + j < p.k * p.ℓ) (hck : slotChk p e j = true) {s : State}
    (hs : GS p h e j σ s) : WP isa (.block (setSR p e j)) s (GS p h e (j + 1) σ) := by
  have hkl := kl_le p hp
  obtain ⟨hr, hc⟩ := entry_lt hp he
  simp only [slotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  obtain ⟨⟨⟨h32, h33⟩, h3⟩, hk⟩ := hck
  have L := hs.s3.t.lay hp hv
  unfold setSR
  refine WP.mono (setB2At_ok L (oSB4 + 34 * j) h32 h33 ((e + j) % p.ℓ) ((e + j) / p.ℓ) (by omega) (by omega))
    fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ⟨hs.s3.keep hp hv hP₁ h15₁ h3, fun k hk' => ?_⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP₁ (hk k hk'), hs.done k hk']
  · rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hm₁, seed_bytes, hs.s3.rho4 k hj, aSeed, integerToBytes_one,
      integerToBytes_one]

/-- Whether entry `(r', c')` is one of the four from `e`. -/
abbrev inGrp (l e r' c' : Nat) : Bool := decide (e ≤ l * r' + c') && decide (l * r' + c' < e + 4)

/-- The facts about the parameters the entries `e, …, e + 3` need. -/
def gChk (p : Params) (e : Nat) : Bool :=
  (List.range 4).all (fun j => slotChk p e j) && rej4Chk (vB p) (vW p) (pS (20 + e)) (sc (oR4 p)) &&
    inB (vB p) (pS (20 + e)) 4096 && inB (vW p) (pS (20 + e)) 4096 &&
    s3Chk p e (inGrp p.ℓ e) [(pS (20 + e), 4096), (sc (oR4 p), 8192)] && decide (e + 4 ≤ p.k * p.ℓ)

theorem gChk_all : ∀ p ∈ params, ∀ g < p.k * p.ℓ / 4, gChk p (4 * g) = true := by decide

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (pS (20 + e))) k = pa s (pS (20 + (e + k))) := by
  unfold poly4
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show oP (20 + e) + 1024 * k = oP (20 + (e + k)) by
    simp only [oP]; omega]

theorem aGrp_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {g : Nat} (hck : gChk p (4 * g) = true) {s : State}
    (hs : S3 p h (4 * g) σ s) : WP isa (aGrp P p g) s (S3 p h (4 * (g + 1)) σ) := by
  have hkl := kl_le p hp
  simp only [gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hsl, hrej⟩, hin⟩, hwa⟩, hG⟩, hl⟩ := hck
  obtain ⟨hk, kSB, k4, kE⟩ := s3Chk_spec hG
  obtain ⟨tk, hh, zk⟩ := keepChk_spec hk
  unfold aGrp
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega) (hsl 0 (by decide))
    ⟨hs, fun _ h => absurd h (by omega)⟩) fun _ g₁ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega) (hsl 1 (by decide)) g₁) fun _ g₂ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega) (hsl 2 (by decide)) g₂) fun _ g₃ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega) (hsl 3 (by decide)) g₃) fun s₄ g₄ => ?_)
  have L₄ := g₄.s3.t.lay hp hv
  obtain ⟨q, h15, hok, hbad⟩ := g₄.s3.ok
  have hseed : ∀ k < 4, seed4 s₄.mem (pa s₄ (sc oSB4)) k =
      aSeed (vPk p σ) ((4 * g + k) / p.ℓ) ((4 * g + k) % p.ℓ) := fun k hk => by
    unfold seed4
    rw [show pa s₄ (sc oSB4) + BitVec.ofNat 64 (34 * k) = pa s₄ (sc (oSB4 + 34 * k)) by
      simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact g₄.done k hk
  refine WP.mono (sampled4_ok L₄ hin hwa h15 (List.mem_cons_self ..)
    (F := fun k b => rejNTTPoly b.rejNTT (aSeed (vPk p σ) ((4 * g + k) / p.ℓ) ((4 * g + k) % p.ℓ)))
    (WP.mono (rej4At_ok C.rej4 L₄ hrej) fun s' ⟨hP, h15', hred, ho⟩ => ⟨hP, h15', hred, ?_⟩))
    fun s₅ ⟨hP₅, hred₅, rr, hrr, h15₅, hs1, hs0⟩ => ?_
  · rcases ho with ⟨h1, hb⟩ | ⟨h0, k, hk, hn⟩
    · exact .inl ⟨h1, fun k hk => by rw [← hseed k hk]; exact hb k hk⟩
    · exact .inr ⟨h0, k, hk, by rw [← hseed k hk]; exact hn⟩
  have e₅ : ∀ k, poly4 (pa s₄ (pS (20 + 4 * g))) k = pa s₅ (pS (20 + (4 * g + k))) := fun k => by
    rw [pa_poly4, hP₅.pa (show Reg.rbx ∈ bases by decide)]
  have hgrp : ∀ r' c', inGrp p.ℓ (4 * g) r' c' = true → 4 * g ≤ p.ℓ * r' + c' ∧ p.ℓ * r' + c' < 4 * g + 4 :=
    fun r' c' hg => by simp only [inGrp, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg
  have hout : ∀ r' c', Done p.ℓ (4 * (g + 1)) r' c' → inGrp p.ℓ (4 * g) r' c' = false → Done p.ℓ (4 * g) r' c' :=
    fun r' c' hd hx => by
      simp only [inGrp, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx
      unfold Done at hd ⊢
      omega
  refine ⟨g₄.s3.t.step hp hv hP₅ tk, L₄.keepHint hP₅ hh g₄.s3.hint,
    fun i hi => L₄.keepPoly hP₅ (zk i hi) (g₄.s3.z i hi), by rw [L₄.keepBytes hP₅ kSB, g₄.s3.rho],
    fun k hk => by rw [L₄.keepBytes hP₅ (k4 k hk), g₄.s3.rho4 k hk], fun r' hr' c' hc' hd => ?_,
    q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩
  · cases hx : inGrp p.ℓ (4 * g) r' c'
    · exact L₄.keepRed hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx) (g₄.s3.red r' hr' c' hc' (hout r' c' hd hx))
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      have := hred₅ (p.ℓ * r' + c' - 4 * g) (by omega)
      rwa [e₅, show 4 * g + (p.ℓ * r' + c' - 4 * g) = p.ℓ * r' + c' by omega, ← pA_eq] at this
  · rw [h15₅]
    exact flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    cases hx : inGrp p.ℓ (4 * g) r' c'
    · obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' (hout r' c' hd hx)
      exact ⟨b, by rw [hb, L₄.keepPolyAt hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx)]⟩
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      obtain ⟨b, hb⟩ := hs1 hq.2 (p.ℓ * r' + c' - 4 * g) (by omega)
      obtain ⟨er, ec⟩ := rc_eq hc' (show p.ℓ * r' + c' = 4 * g + (p.ℓ * r' + c' - 4 * g) by omega)
      rw [← er, ← ec, e₅, show 4 * g + (p.ℓ * r' + c' - 4 * g) = p.ℓ * r' + c' by omega, ← pA_eq] at hb
      exact ⟨b, hb⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', by unfold Done at hd ⊢; omega, hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      obtain ⟨k, hk, hn⟩ := hs0 h0
      obtain ⟨hr, hc⟩ := entry_lt hp (show 4 * g + k < p.k * p.ℓ by omega)
      exact ⟨_, hr, _, hc, by unfold Done; have := Nat.div_add_mod (4 * g + k) p.ℓ; omega, hn⟩

/-- After the samplers, with the hint `h`. -/
structure S4 (p : Params) (h : List (Vector Bool n)) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  red : ∀ r < p.k, ∀ c < p.ℓ, Reduced st.mem (pa st (pA p.ℓ r c))
  redC : Reduced st.mem (pa st pC)
  ok : ∃ q : Bool, st.gpr .r15 = flag (q = true) ∧
    (q = true → (∀ r < p.k, ∀ c < p.ℓ,
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r c) = some (polyAt st.mem (pa st (pA p.ℓ r c)))) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (vCt p (vSig p σ))).map toRq = some (polyAt st.mem (pa st pC))) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r c) = none) ∨
      (sampleInBall p.τ minBounds.ball (vCt p (vSig p σ))).map toRq = none)

abbrev wsC : List (Ptr × Nat) := [(pC, 1024), (sc oSS, 2048)]

/-- The facts about the parameters the copy of `ρ` and `c` need. -/
def sChk (p : Params) : Bool :=
  sepB (vB p) (.rbp, 0) 32 (sc oSB) 32 && inB (vW p) (sc oSB) 32 && keepChk p [(sc oSB, 32)] &&
    decide (32 ≤ p.pkLen) && ballChk (vB p) (vW p) (.r13, 0) p.ctildeLen pC &&
    decide ((p.ctildeLen, p.τ) ∈ ballParams) && decide (p.ctildeLen ≤ p.sigLen) && keepChk p wsC &&
    inB (vB p) pC 1024 && inB (vW p) pC 1024 &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => keepB (vB p) wsC (pA p.ℓ r c) 1024)

theorem sChk_all : ∀ p ∈ params, sChk p = true := by decide

/-- After `ρ` is copied to `SB` and the first `j` seeds of `SB4`. -/
structure RhoS (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  rho : bytesAt st.mem (pa st (sc oSB)) 32 = vRho (vPk p σ)
  rho4 : ∀ k < j, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 32 = vRho (vPk p σ)
  f15 : st.gpr .r15 = flag True

theorem copyRho_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa (copy (sc oSB) (.rbp, 0) 32) s (RhoS p h 0 σ) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  obtain ⟨t3, h3, z3⟩ := keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  have t₁ := hs.t.step hp hv hP₁ t3
  refine ⟨t₁, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15₁, h15]⟩
  rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hcp, hs.t.pkSlice c4, List.drop_zero]
  rfl

/-- What copying `ρ` to seed `j` of `SB4` needs. -/
def rChk (p : Params) (j : Nat) : Bool :=
  sepB (vB p) (.rbp, 0) 32 (sc (oSB4 + 34 * j)) 32 && inB (vW p) (sc (oSB4 + 34 * j)) 32 &&
    keepChk p [(sc (oSB4 + 34 * j), 32)] && keepB (vB p) [(sc (oSB4 + 34 * j), 32)] (sc oSB) 32 &&
    (List.range j).all (fun k => keepB (vB p) [(sc (oSB4 + 34 * j), 32)] (sc (oSB4 + 34 * k)) 32)

theorem rChk_all : ∀ p ∈ params, ∀ j < 4, rChk p j = true := by decide

theorem copyK_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)} {j : Nat}
    (hj : j < 4) {s : State} (hs : RhoS p h j σ s) :
    WP isa (copy (sc (oSB4 + 34 * j)) (.rbp, 0) 32) s (RhoS p h (j + 1) σ) := by
  have hc := rChk_all p hp j hj
  simp only [rChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  have hpk : 32 ≤ p.pkLen := by
    have := sChk_all p hp
    simp only [sChk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1.2
  obtain ⟨t3, h3, z3⟩ := keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  refine ⟨hs.t.step hp hv hP₁ t3, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi),
    by rw [L.keepBytes hP₁ c4, hs.rho], fun k hk => ?_, by rw [h15₁, hs.f15]⟩
  rcases (by omega : k < j ∨ k = j) with hk | rfl
  · rw [L.keepBytes hP₁ (c5 k hk), hs.rho4 k hk]
  · rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hcp, hs.t.pkSlice hpk, List.drop_zero]
    rfl

theorem RhoS.s3 {p : Params} {h : List (Vector Bool n)} {σ s : State} (r : RhoS p h 4 σ s) : S3 p h 0 σ s :=
  ⟨r.t, r.hint, r.z, r.rho, r.rho4, fun r' _ c' _ hd => absurd hd (by unfold Done; omega),
    true, by rw [r.f15]; exact flag_congr (by simp), fun _ r' _ c' _ hd => absurd hd (by unfold Done; omega),
    fun hq => absurd hq (by simp)⟩

theorem rhos_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa rhos s (S3 p h 0 σ) := by
  unfold rhos
  refine WP.seq (WP.mono (copyRho_ok hp hv hs h15) fun s₀ r₀ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 0) (by decide) r₀) fun s₁ r₁ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 1) (by decide) r₁) fun s₂ r₂ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 2) (by decide) r₂) fun s₃ r₃ => ?_)
  exact WP.mono (copyK_ok hp hv (j := 3) (by decide) r₃) fun _ r₄ => r₄.s3

theorem ballStage_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s₂ : State} (hs₂ : S3 p h (p.k * p.ℓ) σ s₂) :
    WP isa (sampled (ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC) s₂ (S4 p h σ) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩ := hc
  obtain ⟨t8, h8, z8⟩ := keepChk_spec c8
  have L₂ := hs₂.t.lay hp hv
  obtain ⟨q, h15₂, hok, hbad⟩ := hs₂.ok
  refine WP.mono (sampled_ok L₂ c9 c10 h15₂ (List.mem_cons_self ..)
    (WP.mono (ballAt_ok C.ball L₂ c6 c5) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₃ ⟨hP₃, hred, rr, hrr, h15₃, hs1, hs0⟩ => ?_
  have hct : bytesAt s₂.mem (pa s₂ (.r13, 0)) p.ctildeLen = vCt p (vSig p σ) := by
    rw [hs₂.t.sigSlice (by omega), List.drop_zero]; rfl
  rw [hct] at hs1 hs0
  have hdone : ∀ r' c', r' < p.k → c' < p.ℓ → Done p.ℓ (p.k * p.ℓ) r' c' := fun _ _ hr hc => done_all hr hc
  have ec : pa s₃ pC = pa s₂ pC := hP₃.pa (show Reg.rbx ∈ bases by decide)
  refine ⟨hs₂.t.step hp hv hP₃ t8, L₂.keepHint hP₃ h8 hs₂.hint, fun i hi => L₂.keepPoly hP₃ (z8 i hi) (hs₂.z i hi),
    fun r hr c hc => L₂.keepRed hP₃ (c11 r hr c hc) (hs₂.red r hr c hc (hdone r c hr hc)), by rw [ec]; exact hred,
    q && (rr == 1), by rw [h15₃]; exact flag_congr (by cases q <;> simp), fun hq => ?_, fun hq => ?_⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨fun r hr c hc => ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hok hq.1 r hr c hc (hdone r c hr hc)
      exact ⟨b, by rw [hb, L₂.keepPolyAt hP₃ (c11 r hr c hc)]⟩
    · obtain ⟨b, hb⟩ := hs1 hq.2
      exact ⟨b, by rw [hb, ec]⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', _, hn⟩ := hbad hq'
      exact .inl ⟨r', hr', c', hc', hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact .inr (hs0 h0)

theorem samples_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa (samples P p) s (S4 p h σ) := by
  unfold samples
  refine WP.seq (WP.mono (rhos_ok hp hv hs h15) fun s₁ s₁3 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun g => S3 p h (4 * g) σ) (p.k * p.ℓ / 4) 0
    (fun g _ hg st hst => aGrp_ok C hp hv (gChk_all p hp g (by omega)) hst) s₁ s₁3) fun s₂ hs₂ => ?_)
  rw [Nat.zero_add] at hs₂
  refine WP.seq (WP.mono (seqR_ok (I := fun e => S3 p h e σ) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    (fun e _ he st hst => aOne_ok C hp hv (by omega) hst) s₂ hs₂) fun s₃ hs₃ => ?_)
  rw [Nat.div_add_mod] at hs₃
  exact ballStage_ok C hp hv hs₃

end VG.Proof.MlDsa.X86_64.Verify
