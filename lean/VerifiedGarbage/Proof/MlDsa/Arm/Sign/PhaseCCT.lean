import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseC
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.CopyTr

/-!
# ML-DSA signing on ARMv7: the commitment leaks only the pointers

Untrusted: everything here is checked by Lean. Each piece of the
commitment leaks only its pointers, given that its inputs are reduced (and
the coefficients of `HighBits(w[i])` bounded): `maskR_trL`, `rowW_trL`,
`w1R_trL`; so two runs agree on what the commitment leaks (`commit_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- A piece that keeps `I`, from runs in the layout that satisfy it. -/
theorem stepSelf {c : Prog isa} {I : State → Prop}
    (h : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c fun _ _ => True)
    (w : ∀ x, Lay D (sgR p) (sgW p) x → I x → WP isa c x fun x' => (∃ W, PostB D x x' W) ∧ I x') :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c
      fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y :=
  postDep h (F := fun x x' => (∃ W, PostB D x x' W) ∧ I x')
    (fun x y h => ⟨w x h.1.lx h.2.1, w y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (sgB_bases p) hx hy, jx, jy⟩

theorem lrel_r7 {x y : State} (h : LRel D (sgR p) (sgW p) x y) : ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact h.regs (.r7, scrLen p) (by simp [sgR, sgW])

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r : Nat}
    (hr : r < 256) (h1 : inB (rbs ++ wbs) (sc oKAP) 4 = true) (h2 : inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : pa s (sc (oMS + 65)) = pa s (sc (oMS + 64)) + 1 := (pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have ak : State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP) = pa s (sc oKAP) := L.w (p := sc oKAP) h1 (by decide)
  have a64 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 64)) = pa s (sc (oMS + 64)) :=
    L.pa32W (p := sc (oMS + 64)) h2 (by decide)
  have a65 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 65)) = pa s (sc (oMS + 65)) :=
    L.pa32W (p := sc (oMS + 65)) (inB_sub (l := 1) h2 (by decide)) (by decide)
  have c0 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 64))) 1 := by
    have := contains_sub (Region.contains_self (pa s (sc (oMS + 64))) 2) (off := 0) (l := 1) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact contains_sub (Region.contains_self _ 2) (off := 1) (l := 1) (by decide) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMS + 64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (setKappa_ok r hr s (by rw [ak]; exact L.iR h1) (by rw [a64]; exact i0) (by rw [a65]; exact i1))
    fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  rw [ak, a64, a65] at hm
  have hf : Frame [⟨pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  have hg' : ∀ r, r ≠ .r0 → s'.gpr r = s.gpr r := fun r h => hg r (by simpa using h)
  exact ⟨_, (postB_store (D := D) hg' hrd hwr hsp hf).1⟩

theorem maskR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {r : Nat} (hc : mChk p r = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  have hcc := copyChk_spec cc
  unfold maskR
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (block_tr rfl fun x y h => lrel_r7 h.1) (fun x L _ => WP.mono (setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (seqL (J := fun s => Reduced s.mem (pa s (yP p r)))
      (RelCT.mono (maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩)
      (seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
        (RelCT.mono (copy_tr hcc.2.2.2.2.1 hcc.2.2.2.2.2
          fun x y h => ⟨lrel_r7 h.1 _ (List.mem_singleton_self _), lrel_r7 h.1 _ (List.mem_singleton_self _)⟩)
          (fun _ _ h => h) fun _ _ h => h)
        (fun x L hy => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
        (ipAt_tr (t := ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICw p D σ t i x) ∧ ∃ σ, ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, _⟩, hl⟩ := hc
  have hA : ∀ {σ s : State} (I : ICw p D σ t i s) j, j < p.ℓ → Reduced s.mem (pa s (aP p i j)) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [aP_ij]; exact this.1
  let J : State → Prop := fun s => (∃ σ, ICw p D σ t i s) ∧ Reduced s.mem (pa s (wP p i))
  unfold rowW
  refine seqL (J := J) ?_ ?_ (seqL (J := J) ?_ ?_ ?_)
  · refine RelCT.mono (mulAt_tr hP (cm 0 hl)) (fun x y ⟨R, ⟨σ₁, I₁⟩, ⟨σ₂, I₂⟩⟩ =>
      ⟨R, ⟨hA I₁ 0 hl, (I₁.yh 0 hl).1⟩, ⟨hA I₂ 0 hl, (I₂.yh 0 hl).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (mulAt_ok hP L (cm 0 hl) (hA I 0 hl) (I.yh 0 hl).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · refine RelCT.mono (seqR_tr (R := fun _ x y => LRel D (sgR p) (sgW p) x y ∧ J x ∧ J y) (p.ℓ - 1) 1
      fun j hj1 hj => stepSelf ?_ ?_) (fun _ _ h => h) fun _ _ _ => trivial
    · refine RelCT.mono (mulAddAt_tr hP (cm j (by omega))) (fun x y ⟨R, ⟨⟨σ₁, I₁⟩, r₁⟩, ⟨⟨σ₂, I₂⟩, r₂⟩⟩ =>
        ⟨R, ⟨r₁, hA I₁ j (by omega), (I₁.yh j (by omega)).1⟩, ⟨r₂, hA I₂ j (by omega), (I₂.yh j (by omega)).1⟩⟩)
        fun _ _ h => h
    · rintro x L ⟨⟨σ, I⟩, r⟩
      refine WP.mono (mulAddAt_ok hP L (cm j (by omega)) r (hA I j (by omega)) (I.yh j (by omega)).1)
        fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · rintro x L ⟨I, r⟩
    exact WP.mono (seqR_ok (I := fun _ s => ∃ W, PostB D x s W ∧ J s) (p.ℓ - 1) 1
      (fun j hj1 hj s ⟨W, hW, ⟨σ, I'⟩, r'⟩ => WP.mono (mulAddAt_ok hP I'.l.st.lay (cm j (by omega)) r'
        (hA I' j (by omega)) (I'.yh j (by omega)).1) fun x' ⟨hP', _, hq⟩ =>
          ⟨_, hW.trans hP' (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h),
            ⟨σ, I'.step hP' c1⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩) x ⟨[], PostB.refl D x [], I, r⟩)
      fun x' ⟨W, hW, j⟩ => ⟨⟨W, hW⟩, j⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun _ _ h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICh p D σ t i x) ∧ ∃ σ, ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : ICh p D σ t p.k s) :
    WP isa (shakeAt [((.r5, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (shake_ok (sgB_bases p) hP.hD hs h.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (commit P p) (RS p D E fun σ s => IC p D σ t s) := by
  have hc' := hc
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commit
  refine RelCT.seq (R := RS p D E fun σ s => ICw p D σ t 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t p.k s) ?_ ?_))
  · refine RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICm p D σ t r s) p.ℓ 0 fun r _ hr =>
      liftT (fun _ _ h => h.l.st) (fun _ _ _ h => maskR_ok hP (hm r (by omega)) h) (maskR_trL hP (hm r (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICw p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => rowW_ok hP (hw i (by omega)) (by omega) h) (rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [w1Enc]; rfl⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICh p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => w1R_ok hP (hh i (by omega)) (by omega) h) (w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => ctShake_ok hP hc h)
      (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.Arm.Sign
