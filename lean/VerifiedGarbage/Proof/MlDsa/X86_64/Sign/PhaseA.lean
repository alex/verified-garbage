import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsB
import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA signing on x86-64: `ExpandA`

Untrusted: everything here is checked by Lean. `ρ` to `RS`, then entry
`e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from the seed
`ρ ‖ j ‖ i`, with `r15` the AND of the results (`IA`): if it is 1, every
entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one entry's
`RejNTTPoly` does not finish within `minBounds` (`expandA_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
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
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  ok : s.gpr .r15 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (seedE p σ e')).isSome) ∧
    Fam s (aBase p) e (aVal p σ)
  bad : s.gpr .r15 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    integerToBytes_one, integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : pa s (sc a) + BitVec.ofNat 64 b = pa s (sc (a + b)) :=
  VG.Proof.MlKem.X86_64.off_add _ _ _

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
    famChk (sgB p) w2 (aBase p) e && famChk (sgB p) w3 (aBase p) e && rejChk (sgB p) (sgW p) a &&
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
      rejChk (sgB p) (sgW p) (pS (aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
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

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .rbx = s.gpr .rbx) {b m : Nat}
    {f : Nat → Poly} (h : Fam s b m f) : Fam s' b m f := fun j hj => by
  simp only [Pl, pa, hm, hb]; exact h j hj

theorem sampleE_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) : WP isa (sampleE P p e) s (IA p D σ (e + 1)) := by
  obtain ⟨c1, c2, c3, c0, w1, w2, k1, k2, k3, k12, f1, f2, f3, hc, hj, hi⟩ := eChk_spec he
  have L := h.st.lay
  unfold sampleE
  rw [aP_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (setB_okB L (by decide) hj w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (setB_okB S1.lay (by decide) hi w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have hseed : bytesAt s2.mem (pa s2 (sc oRS)) 34 = seedE p σ e := by
    refine seed34 ((S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)) ?_ ?_
    · rw [pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact bytes1_write _ _ _
    · rw [pa_sc_add, hm2, hP2.pa (by decide)]; exact bytes1_write _ _ _
  refine WP.seq (WP.mono (rejCall_ok hP S2.lay hc) fun s3 ⟨hP3, hcs3, hred, hout, hmax⟩ => ?_)
  rw [hseed] at hout hmax
  have S3 := S2.step hP3 c3
  refine WP.mono (and15_ok s3) fun s4 ⟨h15, hm4, k4⟩ => ?_
  have hP4 : PPostB D s3 s4 [] := (postB15 k4 hm4 _).1
  have e15 : s3.gpr .r15 = s.gpr .r15 := by
    rw [hcs3 _ (by decide), hcs2 _ (by decide), hcs1 _ (by decide)]
  rw [e15] at h15
  have hr := outcome01 hout
  have hb4 : s4.gpr .rbx = s2.gpr .rbx := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [hm4, hP4.pa (by decide), S2.lay.keepBytes hP3 k3, S1.lay.keepBytes hP2 k2, L.keepBytes hP1 k1, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s.gpr .r15 = 1 ∧ (s3.gpr .rax).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq hm4 (hP4.bs _ (by decide))
        (Fam.keep S2.lay hP3 f3 (Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)))
    · show PolyIs s4.mem (pa s4 (pS (aBase p + e))) (aVal p σ e)
      rw [hm4, show pa s4 (pS (aBase p + e)) = pa s2 (pS (aBase p + e)) by simp only [pa, hb4]]
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

/-! ## The matrix -/

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (eChk p) && copyChk (sgB p) (sgW p) (sc oRS) (.rbp, 0) 32 &&
    stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen)

theorem aChk_ok {p : Params} (h : Ok3 p) : aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .r15 = 1) : WP isa (Impl.MlDsa.X86_64.Sign.expandA P p) s (IA p D σ (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine WP.seq (WP.mono (copy_okB hs.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .r15 = 1 := by rw [hcs1 _ (by decide), h15]
  have I0 : IA p D σ 0 s1 := ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  have := seqR_ok (f := sampleE P p) (I := IA p D σ) (p.k * p.ℓ) 0
    (fun k _ hk s h => sampleE_ok hP (he k (by omega)) h) s1 I0
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.X86_64.Sign
