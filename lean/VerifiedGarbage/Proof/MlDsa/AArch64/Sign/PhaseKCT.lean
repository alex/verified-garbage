import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

/-!
# ML-DSA signing on AArch64: the checks leak only the pointers and whether they passed

Each check leaks only its pointers, given that its inputs are reduced
(`zR_trL`, `r0R_trL`, `hR_trL`); the branch on their result leaks whether the
iteration passed, which two runs agree on when they agree on what the
iteration leaks (`checks_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
include hP

theorem normAt_post {s : State} (L : Lay D (sgR p) (sgW p) s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : normChk (sgB p) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] := by
  refine WP.seq (WP.mono (normCall_ok hP L hB hc hr) fun s1 ⟨hP1, _, _⟩ => ?_)
  exact WP.mono (and24_ok s1) fun s2 ⟨k2, _⟩ => PPostB.trans hP1 (postB24 k2 _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)

theorem normAt_trL {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk (sgB p) f = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (normAt P f B)
      fun _ _ => True :=
  seqL (J := fun _ => True) (normCall_tr hP hc)
    (fun x L hr => WP.mono (normCall_ok hP L hB hc hr) fun _ h => ⟨⟨_, h.1⟩, trivial⟩)
    (lrel_tr (fun x y h => h.1) (by taint_decide))

/-! ## `z` -/

theorem zR_trL {t r : Nat} (hc : zChk p r = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IZ p D σ t r x) ∧ ∃ σ, IZ p D σ t r y) (zR P p r)
      fun _ _ => True := by
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩, hr⟩ := hc
  unfold zR
  refine seqL (J := fun s => (∃ σ, IZb p D σ t r s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
    (seqL (J := fun s => (∃ σ, IZb p D σ t r s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s (yP p r))) ?_ ?_ (normAt_trL hP hB cn)))
  · exact RelCT.mono (mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s1 r hr).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s1 r hr).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s1 r hr).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (addAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.y 0 (by omega)).1, r₁⟩, ⟨(I₂.y 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (addAt_ok hP L ca (I.y 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩

/-! ## `r₀` -/

theorem r0R_trL {t i : Nat} (hc : rChk p i = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IR p D σ t i x) ∧ ∃ σ, IR p D σ t i y) (r0R P p i)
      fun _ _ => True := by
  simp only [rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  unfold r0R
  refine seqL (J := fun s => (∃ σ, IRb p D σ t i s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
    (seqL (J := fun s => (∃ σ, IRb p D σ t i s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s (wP p i))) ?_ ?_
        (seqL (J := fun s => Reduced s.mem (pa s t2P)) ?_ ?_ (normAt_trL hP hB cn))))
  · exact RelCT.mono (mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s2 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s2 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s2 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (subAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.w 0 (by omega)).1, r₁⟩, ⟨(I₂.w 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (subAt_ok hP L ca (I.w 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · exact lowBitsAt_tr hP hγ cl
  · intro x L r1
    exact WP.mono (lowBitsAt_ok hP L hγ cl r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases 2)]; exact hq.1⟩

/-! ## `ct₀` and `h` -/

theorem hR_trL {t i : Nat} (hc : hChk2 p i = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IH p D σ t i x) ∧ ∃ σ, IH p D σ t i y) (hR P p i)
      fun _ _ => True := by
  simp only [hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, _⟩, g6⟩, _⟩, _⟩,
    _⟩, _⟩, o1⟩, o2⟩, o3⟩, o4⟩, _⟩, _⟩, t3⟩, t4⟩, u5⟩, _⟩, _⟩, _⟩, hγ'⟩, hγ⟩, hi⟩, _⟩ := hc
  have f6 : keepB (sgR p) (sgW p) [(t4P, 1024)] (wP p i) 1024 = true := by
    simp only [hfam, Bool.and_eq_true] at g6
    exact famChk_one (b := wBase p) g6.1.1.2 (show i < i + 1 by omega)
  let J : State → Prop := fun s => (∃ σ, IHb p D σ t i i s) ∧ Reduced s.mem (pa s t3P)
  unfold hR
  refine seqL (J := J) ?_ ?_ (seqL (J := J) ?_ ?_ (seqL (J := J) ?_ ?_
    (seqL (J := fun s => J s ∧ Reduced s.mem (pa s t4P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s t4P) ∧ Reduced s.mem (pa s (wP p i))) ?_ ?_
        (seqL (J := fun s => Reduced s.mem (pa s t4P) ∧ Reduced s.mem (pa s (wP p i))) ?_ ?_
          (seqL (J := fun _ => True) ?_ ?_ ?_))))))
  · exact RelCT.mono (mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.t0 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.t0 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.t0 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' g1 o1⟩, by rw [hP'.pa (pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g2 o2⟩, by rw [hP'.pa (pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (normAt_trL hP hγ' cn) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (normAt_post hP L hγ' cn r1) fun x' hP' => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g3 o3⟩, L.keepRed hP' t3 r1⟩
  · exact copy_tr (.inl rfl) rfl fun x y h => h.1
  · rintro x L ⟨⟨σ, I⟩, r3⟩
    exact WP.mono (copy_ok L cc) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, ⟨⟨σ, I.step hP' g4 o4⟩, L.keepRed hP' t4 r3⟩,
      by rw [hP'.pa (pS_bases 4)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.w' 0 (by omega)).1⟩
  · exact RelCT.mono (addAt_tr hP ca) (fun x y ⟨R, ⟨⟨⟨_, I₁⟩, r₁⟩, _⟩, ⟨⟨⟨_, I₂⟩, r₂⟩, _⟩⟩ =>
      ⟨R, ⟨(I₁.w' 0 (by omega)).1, r₁⟩, ⟨(I₂.w' 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨⟨σ, I⟩, r3⟩, r4⟩
    exact WP.mono (addAt_ok hP L ca (I.w' 0 (by omega)).1 r3) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, L.keepRed hP' u5 r4, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · exact RelCT.mono (subAt_tr hP cs) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (subAt_ok hP L cs r4 rw) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases 4)]; exact hq.1, L.keepRed hP' f6 rw⟩
  · exact RelCT.mono (hintCall_tr hP hγ ch) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩)
      fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (hintCall_ok hP L hγ ch r4 rw) fun x' ⟨hP', _, _⟩ => ⟨⟨_, hP'⟩, trivial⟩
  · exact lrel_tr (fun x y h => h.1) (by taint_decide)

/-! ## The checks -/

omit hP in
theorem onesOk_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (onesOk p)) (.block [])).isSome = true := by
  dsimp only [onesOk]; rfl

omit hP in
theorem kapAdd_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (kapAdd p)) (.block [])).isSome = true := by
  dsimp only [kapAdd]; rfl

theorem checks_tr (hc : ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome → (PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t))) :
    RelCT isa (RS p D E fun σ s => KA p D σ t s) (checks P p)
      (RS p D E fun σ s => EP p D σ t s ∨ EF p D σ t s) := by
  refine ksChk_spec hc fun c1 _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine RelCT.seq (R := RS p D E fun σ s => KN p D σ t s)
    (liftL (T := fun s => Reduced s.mem (pa s cP)) (fun σ s h => ⟨h.c.l.st, h.cc.1⟩)
      (fun _ _ _ h => cntt_ok hP hc h) (ipAt_tr (t := ntt) hP.ntt c1)) ?_
  refine RelCT.seq (R := RS p D E fun σ s => IZ p D σ t 0 s)
    (liftT (fun _ _ h => h.b.l.st) (fun _ _ _ h => kInit_ok hc h) (lrel_tr (fun x y h => h) (by taint_decide))) ?_
  refine RelCT.seq (R := RS p D E fun σ s => IR p D σ t 0 s) (RelCT.mono (seqR_tr (Q := fun r => RS p D E
    fun σ s => IZ p D σ t r s) p.ℓ 0 fun r _ hr => liftL (T := fun s => ∃ σ, IZ p D σ t r s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => zR_ok hP (hz r (by omega)) h) (zR_trL hP (hz r (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ir) ?_
  refine RelCT.seq (R := RS p D E fun σ s => IH p D σ t 0 s) (RelCT.mono (seqR_tr (Q := fun i => RS p D E
    fun σ s => IR p D σ t i s) p.k 0 fun i _ hi => liftL (T := fun s => ∃ σ, IR p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => r0R_ok hP (hr i (by omega)) h) (r0R_trL hP (hr i (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ih) ?_
  refine RelCT.seq (R := RS p D E fun σ s => IH p D σ t p.k s) (RelCT.mono (seqR_tr (Q := fun i => RS p D E
    fun σ s => IH p D σ t i s) p.k 0 fun i _ hi => liftL (T := fun s => ∃ σ, IH p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => hR_ok hP (hh i (by omega)) h) (hR_trL hP (hh i (by omega))))
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.seq (R := RS p D E fun σ s => KO p D σ t s)
    (liftT (fun _ _ h => h.1.b.l.st) (fun _ _ _ h => onesOk_ok hc h) (lrel_tr (fun x y h => h) (onesOk_taint p))) ?_
  refine liftR (fun _ _ _ h => kBranch_ok hc h) (ifOkElse_tr (fun x y h => ?_)
    (lrel_tr (fun x y h => h.1.lrel fun _ _ h => h.b.l.st) (by taint_decide))
    (lrel_tr (fun x y h => h.1.lrel fun _ _ h => h.b.l.st) (kapAdd_taint p)))
  obtain ⟨σ₁, σ₂, _, _, _, he, k₁, k₂⟩ := h
  rw [k₁.x24, k₂.x24, bit_congr (hE σ₁ σ₂ he k₁.b.some k₂.b.some)]

end

end VG.Proof.MlDsa.AArch64.Sign
