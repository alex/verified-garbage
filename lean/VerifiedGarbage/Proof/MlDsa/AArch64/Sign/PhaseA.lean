import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Prims
import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA signing on AArch64: `ExpandA`

Untrusted: everything here is checked by Lean. `ρ` to `RS`, then entry
`e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from the seed
`ρ ‖ j ‖ i`, with `x24` the AND of the results (`IA`): if it is 1, every
entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one entry's
`RejNTTPoly` does not finish within `minBounds` (`expandA_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ) = pS (5 + 4 * p.k + 3 * p.ℓ + e)
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

theorem Fam.snoc {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b m f) (h' : Pl s (b + m) (f m)) :
    Fam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  st : St p D σ s
  rs : bytesAt s.mem (pa s (sc oRS)) 32 = rhoOf p σ
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  ok : s.gpr .x24 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (seedE p σ e')).isSome) ∧
    Fam s (aBase p) e (aVal p σ)
  bad : s.gpr .x24 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    integerToBytes_one, integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : pa s (sc a) + BitVec.ofNat 64 b = pa s (sc (a + b)) := by
  rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

/-! ## An entry -/

/-- What entry `e` needs of the layout. -/
def eChk (p : Params) (e : Nat) : Bool :=
  let a := pS (aBase p + e)
  let w1 : List (Ptr × Nat) := [(sc (oRS + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS + 33), 1)]
  let w3 : List (Ptr × Nat) := [(a, 1024), (sc oPS, 2048)]
  stChk p w1 && stChk p w2 && stChk p w3 && stChk p [] && inB (sgW p) (sc (oRS + 32)) 1 &&
    inB (sgW p) (sc (oRS + 33)) 1 && keepB (sgB p) w1 (sc oRS) 32 && keepB (sgB p) w2 (sc oRS) 32 &&
    keepB (sgB p) w3 (sc oRS) 32 && keepB (sgB p) w2 (sc (oRS + 32)) 1 && famChk (sgB p) w1 (aBase p) e &&
    famChk (sgB p) w2 (aBase p) e && famChk (sgB p) w3 (aBase p) e && rejChkS (sgR p) (sgW p) a &&
    decide (e % p.ℓ < 256) && decide (e / p.ℓ < 256)

theorem eChk_spec {p : Params} {e : Nat} (h : eChk p e = true) :
    stChk p [(sc (oRS + 32), 1)] = true ∧ stChk p [(sc (oRS + 33), 1)] = true ∧
      stChk p [(pS (aBase p + e), 1024), (sc oPS, 2048)] = true ∧ stChk p [] = true ∧
      inB (sgW p) (sc (oRS + 32)) 1 = true ∧ inB (sgW p) (sc (oRS + 33)) 1 = true ∧
      keepB (sgB p) [(sc (oRS + 32), 1)] (sc oRS) 32 = true ∧ keepB (sgB p) [(sc (oRS + 33), 1)] (sc oRS) 32 = true ∧
      keepB (sgB p) [(pS (aBase p + e), 1024), (sc oPS, 2048)] (sc oRS) 32 = true ∧
      keepB (sgB p) [(sc (oRS + 33), 1)] (sc (oRS + 32)) 1 = true ∧
      famChk (sgB p) [(sc (oRS + 32), 1)] (aBase p) e = true ∧ famChk (sgB p) [(sc (oRS + 33), 1)] (aBase p) e = true ∧
      famChk (sgB p) [(pS (aBase p + e), 1024), (sc oPS, 2048)] (aBase p) e = true ∧
      rejChkS (sgR p) (sgW p) (pS (aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
  simp only [eChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem outcome01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α} (h : Outcome f r out) :
    r = 1 ∨ r = 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .x28 = s.gpr .x28) {b m : Nat}
    {f : Nat → Poly} (h : Fam s b m f) : Fam s' b m f := fun j hj => by
  simp only [Pl, pa, hm, hb]; exact h j hj

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

theorem blkE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : eChk p e = true) {s : State}
    (h : IA p D σ e s) : WP isa (.block (blkE p e)) s fun s' =>
      (IA p D σ e s' ∧ bytesAt s'.mem (pa s' (sc oRS)) 34 = seedE p σ e) ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨c1, c2, _, _, w1, w2, k1, k2, _, k12, f1, f2, _, _, hj, hi⟩ := eChk_spec he
  have L := h.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (by decide) w1 (by decide)) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (setB_ok S1.lay (by decide) w2 (by decide)) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have e15 : s2.gpr .x24 = s.gpr .x24 := by rw [hcs2.get .x24, hcs1.get .x24]
  have hrs : bytesAt s2.mem (pa s2 (sc oRS)) 32 = rhoOf p σ :=
    (S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)
  refine ⟨⟨⟨S2, hrs, e15 ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (e15 ▸ h0)⟩, seed34 hrs ?_ ?_⟩, e15⟩
  · obtain ⟨ok, fam⟩ := h.ok (e15 ▸ h1)
    exact ⟨ok, Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)⟩
  · rw [pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact bytes1_write _ _ _
  · rw [pa_sc_add, hm2, hP2.pa (by decide)]; exact bytes1_write _ _ _

/-- What the call of entry `e` leaves. -/
def CallE (D : Nat) (a : Ptr) (x : List Byte) (s s' : State) : Prop :=
  PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
    ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT x) ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s a)) ∧
    ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT x).isSome)

/-- Entry `e`'s call is done. -/
def JE (p : Params) (D : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, IA p D σ e s₀ ∧ CallE D (pS (aBase p + e)) (seedE p σ e) s₀ s

theorem callE_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (aBase p + e))),
      (.x2, .ptr (sc oPS))]) s
      (JE p D e σ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ => ⟨s, h, hP3, hcs3, hred, ?_, ?_⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem andE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : eChk p e = true) {s : State}
    (h : JE p D e σ s) : WP isa (.block and24) s (IA p D σ (e + 1)) := by
  obtain ⟨_, _, c3, c0, _, _, _, _, k3, _, _, _, f3, _, _, _⟩ := eChk_spec he
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := h
  have S3 := h.st.step hP3 c3
  refine WP.mono (and24_ok s) fun s4 ⟨k4, h15⟩ => ?_
  have hm4 : s4.mem = s.mem := k4.mem
  have hP4 : PPostB D s s4 [] := postB24 k4 _
  rw [hcs3] at h15
  have hr := outcome01 hout
  have hb4 : s4.gpr .x28 = s₀.gpr .x28 := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [hm4, hP4.pa (by decide), h.st.lay.keepBytes hP3 k3, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .x24 = 1 ∧ (s.gpr .x0).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep h.st.lay hP3 f3 fam)
    · show PolyIs s4.mem (pa s4 (pS (aBase p + e))) (aVal p σ e)
      rw [hm4, show pa s4 (pS (aBase p + e)) = pa s₀ (pS (aBase p + e)) by simp only [pa, hb4]]
      exact ⟨hred hs.2, rej_val hout hs.2 hm⟩
  · rw [h15] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega, hn⟩

theorem sampleE_eq (P : Prims) (p : Params) (e : Nat) : sampleE P p e = .seq (.block (blkE p e))
    (.seq (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (aBase p + e))),
      (.x2, .ptr (sc oPS))]) (.block and24)) := by
  unfold sampleE rejAt; rw [aP_eq]

theorem sampleE_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) : WP isa (sampleE P p e) s (IA p D σ (e + 1)) := by
  rw [sampleE_eq]
  exact WP.seq (WP.mono (blkE_ok he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (callE_ok hP he h1 hs1) fun s2 h2 => andE_ok he h2))

/-! ## The matrix -/

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (eChk p) && copyPChk (sgB p) (sgW p) (sc oRS) (.x25, 0) &&
    stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen)

theorem aChk_ok {p : Params} (h : Ok3 p) : aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .x24 = 1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s (IA p D σ (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h15]
  have I0 : IA p D σ 0 s1 := ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  have := seqR_ok (f := sampleE P p) (I := IA p D σ) (p.k * p.ℓ) 0
    (fun k _ hk s h => sampleE_ok hP (he k (by omega)) h) s1 I0
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.AArch64.Sign
