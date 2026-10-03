import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly coeffAt polyAt Reduced PolyIs poly4 seed4 minBounds)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oSA4)) k = seedA (rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4) + BitVec.ofNat 64 (34 * k) = pa s (sc (oSA4 + 34 * k)) from sc_add _ _ _]
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
  rw [show 34 * 0 = 0 from rfl, VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-! ## The four polynomials -/

theorem coeffAt_poly4 (m : Mem) (a : Addr) (k j : Nat) : coeffAt m (poly4 a k) j = coeffAt m a (256 * k + j) := by
  unfold coeffAt poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega]

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (aP e)) k = pa s (aP (e + k)) := by
  unfold poly4
  rw [show pa s (aP e) + BitVec.ofNat 64 (1024 * k) = pa s (sc (oP e + 1024 * k)) from sc_add _ _ _,
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


theorem call_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {σ : State} (hp : kgPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State}
    (h : GS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (mask4 (aP (4*g))))) s (KSamp p σ (4*g+4) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := aP (4*g)) (ss := sc (oR4 p)) (by unfold rej4Chk; lay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩
    exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide)
    (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by
    rw [h20.get .x0]; exact hr01
  refine WP.mono (mask4_ok L20 (a := aP (4*g)) (by lay) (by lay) hr20)
    fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (4*g)) = pa s (aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (aP (4*g)) = pa s2 (aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4, ∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (aP (4*g+k)) = poly4 (pa s (aP (4*g))) k := fun k => by
    rw [pa_poly4,sc_pa hP13]
  obtain ⟨A,S',hA,_,hG⟩ := h.ks.ex
  have h24' : s3.gpr .x24 = if s.gpr .x24 = 1 ∧ (s2.gpr .x0).setWidth 32 = 1 then 1 else 0 := by
    rw [k3.get .x24,e24,h24,Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01]
  refine ⟨h.ks.k1.step hF hp hP13 (by unfold k1Chk kcChk; lay),
    fun e' => if e' < 4*g then A e' else polyAt s3.mem (pa s3 (aP e')),S',
    fun e' he' => ?_,fun _ h => False.elim (Nat.not_lt_zero _ h),?_⟩
  · dsimp only
    by_cases hlt : e' < 4*g
    · rw [ifp hlt]
      exact L.keepPoly hP13 (by lay) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_,rfl⟩
      obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega⟩
      rw [e3]
      by_cases h1 : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega))).2 (hred h1 k (by omega))
      · exact (masked_zero h1 (hco4 k (by omega))).1
  · rw [h24']
    rcases hG with ⟨h1,b,hb,_⟩ | ⟨h0,hn⟩
    · rcases hout with ⟨ho,hb4⟩ | ⟨ho,k,hk,hn⟩
      · obtain ⟨n,hn⟩ := bound4 hb4
        refine .inl ⟨by rw [ifp ⟨h1,ho⟩],{ b with rejNTT := max b.rejNTT n },fun e' he' => ?_,
          fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
        dsimp only
        by_cases hlt : e' < 4*g
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega⟩
          have hk : k < 4 := by omega
          rw [e3,(masked_one ho (hco4 k hk)).1,← seed4_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [seed4_eq h hk] at hn
        have hq : (4*g+k)/p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega)
        exact .inr ⟨rfl,Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega)) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl,hn⟩

theorem mask4_taint : ∀ j < 80,(taint.check (Taint.ofRegs [.x28]) (mask4 (sc (oP j)))
    (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (mask4 (sc 0)))).isSome = true := by decide +kernel

theorem tail4_tr {p : Params} {S j : Nat} (hj : j < 80) :
    RelCT isa (Two p S) (.seq (.block and24) (mask4 (aP j))) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by
    simp only [and24,List.mem_singleton] at hi; subst hi; rfl)
    fun x _ => WP.mono (and24_ok x) fun _ ⟨o,_⟩ =>
      ⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (mask4_taint j hj))

theorem call_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : Piece p S (GS p · (4*g) 4) (KSamp p · (4*g+4) 0)
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
        (.seq (.block and24) (mask4 (aP (4*g))))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => call_ok hP hF hp hg h,
    rel_of (Q := fun x y => Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨kc_two hF hp hp' hq h.ks.k1.kc h'.ks.k1.kc,by
        rw [h.seeds,h'.seeds,rho_pub hq]⟩)⟩
  have hc : rej4Chk kgR (kgW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by
    unfold rej4Chk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (tail4_tr (by omega))

theorem expA4_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) :
    Piece p S (KSamp p · (4*g) 0) (KSamp p · (4*g+4) 0) (expA4 P p g) := by
  unfold expA4
  refine Piece.seq (Piece.mono
    (Piece.seqR (I := fun j σ s => GS p σ (4*g) j s) 4 0
      (fun j _ hj => slot_piece hF hg (by omega)))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (call_piece hP hF hg)

theorem sampAll_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) :
    Piece p S (fun σ s => K1 p σ s ∧ s.gpr .x24 = 1) (KSamp p · (p.k*p.ℓ) 0) (expAll P p) := by
  unfold expAll
  have hB : Piece p S (KSamp p · 0 0) (KSamp p · (4*(p.k*p.ℓ/4)) 0)
      (seqR (expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (Piece.seqR (I := fun g σ s => KSamp p σ (4*g) 0 s) (p.k*p.ℓ/4) 0
        (fun g _ hg => expA4_piece hP hF (by omega)))
  refine Piece.mono (Piece.seq hB
    (Piece.seqR (I := fun e σ s => KSamp p σ e 0 s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he => expA_piece hP hF (by omega))))
    (fun _ _ _ h => KSamp.zero h.1 h.2) (fun _ _ _ h => ?_)
  have he : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [he] using h

end VG.Proof.MlDsa.AArch64.KeyGen
