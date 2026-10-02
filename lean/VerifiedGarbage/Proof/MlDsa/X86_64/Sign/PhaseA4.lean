import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA

/-!
# ML-DSA signing on x86-64: `ExpandA`, four entries at a time

Untrusted: everything here is checked by Lean. `ρ` to `RS` and to each of
the four seeds at `RS4` (`IA4`); then, for each group of four entries
`4g, …, 4g + 3`, their indices to the seeds (`GS`, `slot_ok`) and one call
of `vg_mldsa_rej_ntt_poly4`, ANDed into `r15` (`call4_ok`); then the last
`kℓ mod 4` entries one at a time (`sampleE_ok`). Each step keeps `IA`
(`expandA_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `ExpandA` after `e` entries, with `ρ` in each seed of `RS4`. -/
structure IA4 (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  ia : IA p D σ e s
  rs4 : ∀ k < 4, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 32 = rhoOf p σ

/-- … and the seeds of entries `e, …, e + j - 1` in the first `j` seeds. -/
structure GS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia4 : IA4 p D σ e s
  done : ∀ k < j, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 34 = seedE p σ (e + k)

/-! ## Pieces that keep `IA` -/

theorem IA.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : IA p D σ e s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hst : stChk p ws = true) (hk : keepB (sgB p) ws (sc oRS) 32 = true)
    (hf : famChk (sgB p) ws (aBase p) e = true) (e15 : s'.gpr .r15 = s.gpr .r15) : IA p D σ e s' := by
  refine ⟨h.st.step hP hst, (h.st.lay.keepBytes hP hk).trans h.rs, by rw [e15]; exact h.r01, fun h1 => ?_,
    fun h0 => h.bad (by rw [← e15]; exact h0)⟩
  obtain ⟨ok, fam⟩ := h.ok (by rw [← e15]; exact h1)
  exact ⟨ok, Fam.keep h.st.lay hP hf fam⟩

/-- The seeds of `RS4` apart from `ws`. -/
def rs4Chk (p : Params) (ws : List (Ptr × Nat)) (n : Nat) : Bool :=
  (List.range 4).all fun k => keepB (sgB p) ws (sc (oRS4 + 34 * k)) n

theorem rs4Chk_spec {p : Params} {ws : List (Ptr × Nat)} {n : Nat} (h : rs4Chk p ws n = true) {k : Nat}
    (hk : k < 4) : keepB (sgB p) ws (sc (oRS4 + 34 * k)) n = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem IA4.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : IA4 p D σ e s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hst : stChk p ws = true) (hk : keepB (sgB p) ws (sc oRS) 32 = true)
    (hf : famChk (sgB p) ws (aBase p) e = true) (h4 : rs4Chk p ws 32 = true) (e15 : s'.gpr .r15 = s.gpr .r15) :
    IA4 p D σ e s' :=
  ⟨h.ia.step hP hst hk hf e15, fun k hk => (h.ia.st.lay.keepBytes hP (rs4Chk_spec h4 hk)).trans (h.rs4 k hk)⟩

/-! ## The seeds of a group -/

/-- What seed `j` of entry `e + j` needs of the layout. -/
def slotChk (p : Params) (e j : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 33), 1)]
  stChk p w1 && stChk p w2 && inB (sgW p) (sc (oRS4 + 34 * j + 32)) 1 && inB (sgW p) (sc (oRS4 + 34 * j + 33)) 1 &&
    keepB (sgB p) w1 (sc oRS) 32 && keepB (sgB p) w2 (sc oRS) 32 && famChk (sgB p) w1 (aBase p) e &&
    famChk (sgB p) w2 (aBase p) e && rs4Chk p w1 32 && rs4Chk p w2 32 &&
    keepB (sgB p) w2 (sc (oRS4 + 34 * j + 32)) 1 &&
    (List.range j).all (fun k => keepB (sgB p) w1 (sc (oRS4 + 34 * k)) 34 && keepB (sgB p) w2 (sc (oRS4 + 34 * k)) 34) &&
    decide ((e + j) % p.ℓ < 256) && decide ((e + j) / p.ℓ < 256)

theorem slot_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj4 : j < 4) (hc : slotChk p e j = true) {s : State}
    (h : GS p D σ e j s) : WP isa (.block (setSR p e j)) s fun s' => GS p D σ e (j + 1) s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [slotChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, w1⟩, w2⟩, k1⟩, k2⟩, f1⟩, f2⟩, r1⟩, r2⟩, k12⟩, kd⟩, hj⟩, hi⟩ := hc
  have L := h.ia4.ia.st.lay
  unfold setSR
  rw [WP.block_append_iff]
  refine WP.mono (setB_okB L (show Reg.rbx ≠ .rax by decide) hj w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have e1 : s1.gpr .r15 = s.gpr .r15 := hcs1 _ (by decide)
  have I1 := h.ia4.step hP1 c1 k1 f1 r1 e1
  refine WP.mono (setB_okB I1.ia.st.lay (show Reg.rbx ≠ .rax by decide) hi w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have e2 : s2.gpr .r15 = s1.gpr .r15 := hcs2 _ (by decide)
  have I2 := I1.step hP2 c2 k2 f2 r2 e2
  refine ⟨⟨I2, fun k hk => ?_⟩, e2.trans e1⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · have kk := List.all_eq_true.mp kd k (List.mem_range.mpr hk')
    simp only [Bool.and_eq_true] at kk
    rw [I1.ia.st.lay.keepBytes hP2 kk.2, L.keepBytes hP1 kk.1]
    exact h.done k hk'
  · refine seed34 (I2.rs4 k (by omega)) ?_ ?_
    · rw [pa_sc_add, I1.ia.st.lay.keepBytes hP2 k12, hm1, hP1.pa (show Reg.rbx ∈ bases by decide)]; exact bytes1_write _ _ _
    · rw [pa_sc_add, hm2, hP2.pa (show Reg.rbx ∈ bases by decide)]; exact bytes1_write _ _ _

/-! ## The call -/

theorem pa_poly4 (s : State) (i k : Nat) : poly4 (pa s (pS i)) k = pa s (pS (i + k)) := by
  unfold poly4
  rw [pa_sc_add, show oP i + 1024 * k = oP (i + k) by simp only [oP]; omega]

theorem seed4_eq {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : GS p D σ e 4 s) {k : Nat}
    (hk : k < 4) : seed4 s.mem (pa s (sc oRS4)) k = seedE p σ (e + k) := by
  unfold seed4
  rw [pa_sc_add]; exact h.done k hk

/-- What the call of a group needs of the layout. -/
def callChk (p : Params) (e : Nat) : Bool :=
  let w3 : List (Ptr × Nat) := [(pS (aBase p + e), 4096), (r4P p, 8192)]
  stChk p w3 && stChk p [] && keepB (sgB p) w3 (sc oRS) 32 && rs4Chk p w3 32 && famChk (sgB p) w3 (aBase p) e &&
    rej4Chk (sgB p) (sgW p) (pS (aBase p + e)) (r4P p)

/-- What the call of group `e` leaves. -/
abbrev R4Post (D : Nat) (a w : Ptr) (s s' : State) : Prop :=
  PPostB D s s' [(a, 4096), (w, 8192)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Reduced s'.mem (poly4 (pa s a) k)) ∧
    (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Bounds,
        rejNTTPoly b.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
      ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
        rejNTTPoly minBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = none)) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4,
      (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k)).isSome)

/-- The call of group `e` is done. -/
def J4 (p : Params) (D e : Nat) (σ s : State) : Prop :=
  ∃ s₀, GS p D σ e 4 s₀ ∧ R4Post D (pS (aBase p + e)) (r4P p) s₀ s

theorem callG_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : callChk p e = true) {s : State} (h : GS p D σ e 4 s) :
    WP isa (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (sc oRS4), .ptr (pS (aBase p + e)), .ptr (r4P p)]) s
      fun s' => J4 p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [callChk, Bool.and_eq_true] at hc
  exact WP.mono (rej4Call_ok hP h.ia4.ia.st.lay hc.2) fun s' h' => ⟨⟨s, h, h'⟩, h'.2.1 _ (by decide)⟩

theorem and4_ok {p : Params} {D : Nat} {σ : State} {e : Nat} (hc : callChk p e = true) {s : State}
    (hJ : J4 p D e σ s) : WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s (IA4 p D σ (e + 4)) := by
  simp only [callChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c3, c0⟩, k3⟩, r3⟩, f3⟩, _⟩ := hc
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := hJ
  have L := h.ia4.ia.st.lay
  have I1 := h.ia4.step hP3 c3 k3 f3 r3 (hcs3 _ (by decide))
  refine WP.mono (and15_ok s) fun s4 ⟨h15, hm4, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB15 k4 hm4 _).1
  rw [hcs3 _ (by decide)] at h15
  have hr : (s.gpr .rax).setWidth 32 = 1 ∨ (s.gpr .rax).setWidth 32 = 0 := by
    rcases hout with ⟨h1, _⟩ | ⟨h0, _⟩
    exacts [.inl h1, .inr h0]
  have hb4 : s4.gpr .rbx = s₀.gpr .rbx := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  have epa : ∀ q : Ptr, q.1 = .rbx → pa s4 q = pa s₀ q := fun q hq => by simp only [pa, hq, hb4]
  have hia := h.ia4.ia
  refine ⟨⟨I1.ia.st.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩, fun k hk => ?_⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (by decide), I1.ia.rs]
  · rw [h15]
    rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r15 = 1 ∧ (s.gpr .rax).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := hia.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, fun j hj => ?_⟩
    · by_cases he'' : e' < e
      · exact ok1 e' he''
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ e' = e + k := ⟨e' - e, by omega, by omega⟩
        rw [← seed4_eq h hk]; exact hm k hk
    · by_cases hj' : j < e
      · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep L hP3 f3 fam) j hj'
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ j = e + k := ⟨j - e, by omega, by omega⟩
        show PolyIs s4.mem (pa s4 (pS (aBase p + (e + k)))) (aVal p σ (e + k))
        rw [hm4, epa _ rfl, ← Nat.add_assoc, ← pa_poly4]
        rcases hout with ⟨_, hb⟩ | ⟨h0, _⟩
        · refine ⟨hred hs.2 k hk, ?_⟩
          have := rej_val (x := seed4 s₀.mem (pa s₀ (sc oRS4)) k) (.inl ⟨hs.2, hb k hk⟩) hs.2 (hm k hk)
          rw [this, seed4_eq h hk]; rfl
        · rw [hs.2] at h0; cases h0
  · rw [h15] at h0
    rcases hia.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := hia.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, k, hk, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e + k, by omega, by rw [← seed4_eq h hk]; exact hn⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (show Reg.rbx ∈ bases by decide)]; exact I1.rs4 k hk

theorem call4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : callChk p e = true) {s : State} (h : GS p D σ e 4 s) :
    WP isa (rej4At P (pS (aBase p + e)) (r4P p)) s (IA4 p D σ (e + 4)) := by
  unfold rej4At
  exact WP.seq (WP.mono (callG_ok hP hc h) fun _ h' => and4_ok hc h'.1)

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, VG.Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl,
    VG.Proof.MlKem.bytesAt_add, show 68 = 34 + 34 from rfl, VG.Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds of a group, from `ρ`. -/
theorem GS.seeds {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : GS p D σ e 4 s) :
    bytesAt s.mem (pa s (sc oRS4)) 136 = aSeed (rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      aSeed (rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ aSeed (rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      aSeed (rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (pa s (sc oRS4) + BitVec.ofNat 64 (34 * k)) 34 = seedE p σ (e + k) :=
    fun k hk => seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, BitVec.add_zero] at b0
  rw [bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-- What a group needs of the layout. -/
def g4Chk (p : Params) (e : Nat) : Bool :=
  slotChk p e 0 && slotChk p e 1 && slotChk p e 2 && slotChk p e 3 && callChk p e

theorem sample4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : g4Chk p (4 * g) = true) {s : State} (h : IA4 p D σ (4 * g) s) :
    WP isa (sample4 P p g) s (IA4 p D σ (4 * g + 4)) := by
  simp only [g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine WP.seq (WP.mono (slot_ok (by decide) s0 (j := 0) ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x0 h0 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s1 h0.1) fun x1 h1 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s2 h1.1) fun x2 h2 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s3 h2.1) fun x3 h3 => ?_)
  exact call4_ok hP cc h3.1

/-! ## The matrix -/

/-- `ρ` to `sc o`. -/
theorem copyRho_ok {p : Params} {D : Nat} {σ : State} {o : Nat}
    (hc : copyChk (sgB p) (sgW p) (sc o) (.rbp, 0) 32 = true) (hst : stChk p [(sc o, 32)] = true) (hsk : 32 ≤ p.skLen)
    {s : State} (hs : St p D σ s) :
    WP isa (copy (sc o) (.rbp, 0) 32) s fun s' => St p D σ s' ∧ PPostB D s s' [(sc o, 32)] ∧
      bytesAt s'.mem (pa s' (sc o)) 32 = rhoOf p σ ∧ s'.gpr .r15 = s.gpr .r15 :=
  WP.mono (copy_okB hs.lay hc) fun _ ⟨hP1, hcs1, hb⟩ => ⟨hs.step hP1 hst, hP1,
    by rw [hP1.pa (show Reg.rbx ∈ bases by decide), hb, rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk], hcs1 _ (by decide)⟩

/-- After `ρ` to `RS` and to the first `j` seeds of `RS4`. -/
structure ICopy (p : Params) (D : Nat) (σ : State) (j : Nat) (s : State) : Prop where
  st : St p D σ s
  rs : bytesAt s.mem (pa s (sc oRS)) 32 = rhoOf p σ
  rs4 : ∀ k < j, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 32 = rhoOf p σ
  r15 : s.gpr .r15 = 1

/-- What the copy of `ρ` to seed `j` of `RS4` needs of the layout. -/
def cpChk (p : Params) (j : Nat) : Bool :=
  copyChk (sgB p) (sgW p) (sc (oRS4 + 34 * j)) (.rbp, 0) 32 && stChk p [(sc (oRS4 + 34 * j), 32)] &&
    keepB (sgB p) [(sc (oRS4 + 34 * j), 32)] (sc oRS) 32 &&
    (List.range j).all fun k => keepB (sgB p) [(sc (oRS4 + 34 * j), 32)] (sc (oRS4 + 34 * k)) 32

theorem cpR4_ok {p : Params} {D : Nat} {σ : State} {j : Nat} (hc : cpChk p j = true) (hsk : 32 ≤ p.skLen) {s : State}
    (h : ICopy p D σ j s) : WP isa (cpR4 j) s (ICopy p D σ (j + 1)) := by
  simp only [cpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hcp, hst⟩, k0⟩, kk⟩ := hc
  refine WP.mono (copyRho_ok hcp hst hsk h.st) fun s1 ⟨S1, hP1, hb, e15⟩ =>
    ⟨S1, (h.st.lay.keepBytes hP1 k0).trans h.rs, fun k hk => ?_, e15.trans h.r15⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · exact (h.st.lay.keepBytes hP1 (List.all_eq_true.mp kk k (List.mem_range.mpr hk'))).trans (h.rs4 k hk')
  · exact hb

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (eChk p) && copyChk (sgB p) (sgW p) (sc oRS) (.rbp, 0) 32 &&
    stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen) && (List.range 4).all (cpChk p) &&
    (List.range (p.k * p.ℓ / 4)).all fun g => g4Chk p (4 * g)

theorem aChk_ok {p : Params} (h : Ok3 p) : aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ICopy.ia4 {p : Params} {D : Nat} {σ s : State} (h : ICopy p D σ 4 s) : IA4 p D σ 0 s :=
  ⟨⟨h.st, h.rs, .inr h.r15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans h.r15) (by decide)⟩, h.rs4⟩

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .r15 = 1) : WP isa (Impl.MlDsa.X86_64.Sign.expandA P p) s (IA p D σ (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine WP.seq (WP.mono (copyRho_ok hcp hst hsk hs) fun s1 ⟨S1, _, hb, e15⟩ => ?_)
  have I0 : ICopy p D σ 0 s1 := ⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h15⟩
  refine WP.seq (WP.mono (seqR_ok (f := cpR4) (I := ICopy p D σ) 4 0
    (fun k _ hk s h => cpR4_ok (hc4 k (by omega)) hsk h) s1 I0) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (seqR_ok (f := sample4 P p) (I := fun g => IA4 p D σ (4 * g)) (p.k * p.ℓ / 4) 0
    (fun g _ hg' s h => sample4_ok hP (hg g (by omega)) h) s2 h2.ia4) fun s3 h3 => ?_)
  have := seqR_ok (f := sampleE P p) (I := IA p D σ) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    (fun k h1 hk s h => sampleE_ok hP (he k (by omega)) h) s3 (by rw [Nat.zero_add] at h3; exact h3.ia)
  rwa [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at this

end VG.Proof.MlDsa.X86_64.Sign
