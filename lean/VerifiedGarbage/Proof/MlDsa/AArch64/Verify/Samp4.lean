import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4

/-! Four-way matrix expansion during verification: preserve decoded hints and z, and mask failed batches without a branch. -/

namespace VG.Proof.MlDsa.AArch64.Verify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Reduced polyAt coeffAt poly4 seed4 Bounds rejNTTPoly minBounds)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

structure VS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  va : VA p σ e s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 = seedOf p σ (e+k)

theorem vslot_ok {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ)
    {e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) {s : State} (h : VS p σ e j s) :
    WP isa (seedSlot4 p e j) s (VS p σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_generic L (by vlay) (by vlay) (by vlay)) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.va.keep hF hp hP1 (by vachk hF) (hk1.get .x24)
  have L1 := h1.vz.vc.lay hF hp
  unfold setSR
  refine WP.mono (vsetTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega) (by vlay) (by vlay)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by vachk hF) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by vlay),sc_pa hP2,sc_pa hP1,hb1,h.va.rho,
      sc_add,← sc_pa hP1,hb2,seedOf,Proof.MlDsa.Verify.aSeed,integerToBytes_one,integerToBytes_one,List.append_assoc]
    rfl
  · rw [L1.keepBytes hP2 (by vlay),L.keepBytes hP1 (by vlay)]
    exact h.done k (by omega)

theorem vslot_piece {p : Params} (hF : VFacts p) {S e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) :
    VPiece p S (VS p · e j) (VS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => vslot_ok hF hp he hj h,
    vrel_of (Q := VTwo p S) (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (slot_taint p e hj))
      fun _ _ _ _ hp hp' hq h h' => vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc⟩

theorem vseed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oSA4)) k = seedOf p σ (e+k) := by
  unfold seed4
  rw [show pa s (sc oSA4)+BitVec.ofNat 64 (34*k) = pa s (sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem VS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 4 s) :
    bytesAt s.mem (pa s (sc oSA4)) 136 = seedOf p σ (e+0) ++ seedOf p σ (e+1) ++ seedOf p σ (e+2) ++ seedOf p σ (e+3) := by
  have b : ∀ k < 4,bytesAt s.mem (pa s (sc oSA4)+BitVec.ofNat 64 (34*k)) 34 = seedOf p σ (e+k) :=
    fun k hk => vseed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34*0=0 from rfl,VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [bytes136,b0,b 1 (by decide),b 2 (by decide),b 3 (by decide)]

theorem vcall4_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ : State} (hp : vPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State} (h : VS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (mask4 (aP (4*g))))) s (VA p σ (4*g+4)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := aP (4*g)) (ss := sc (oR4 p)) (by unfold rej4Chk; vlay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (mask4_ok L20 (a := aP (4*g)) (by vlay) (by vlay) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (4*g)) = pa s (aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (aP (4*g)) = pa s2 (aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4,∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (aP (4*g+k)) = poly4 (pa s (aP (4*g))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < 4*g,polyAt s3.mem (pa s3 (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlay)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < 4*g
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega))).2 (hred hret k (by omega))
      · exact (masked_zero hret (hco4 k (by omega))).1
  · rw [k3.get .x24,e24,h24,hq,and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < 4*g
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega)
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega))).1,← vseed4_eq h (by omega)]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega,hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨4*g+k,by omega,by rw [← vseed4_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Verify

namespace VG.Proof.MlDsa.AArch64.Verify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem VTwo.step {p : Params} {S : Nat} {c : Prog isa} {Q : State → State → Prop}
    (hq : ∀ x y,Q x y → VTwo p S x y) (htr : RelCT isa Q c fun _ _ => True)
    (hok : ∀ x y,Q x y → (WP isa c x fun x' => ∃ W,PostB S x x' W) ∧
      (WP isa c y fun y' => ∃ W,PostB S y y' W)) : RelCT isa Q c (VTwo p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W,PostB S x x' W) hok
    fun x y x' y' h ⟨_,hx⟩ ⟨_,hy⟩ => ⟨(hq x y h).lx.post hx,(hq x y h).ly.post hy,
      fun r hr => by rw [hx.bs r hr,hy.bs r hr]; exact (hq x y h).same.1 r hr,
      by rw [hx.sp,hy.sp]; exact (hq x y h).same.2⟩

theorem vcall4_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VS p · (4*g) 4) (VA p · (4*g+4))
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g))) (.seq (.block and24) (mask4 (aP (4*g))))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall4_ok hP hF hp hg h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [h.seeds,h'.seeds]; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej4Chk (vR p) (vW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by unfold rej4Chk; vlay
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (mask4 (aP (4*g)))) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (mask4_taint (4*g) (by omega)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

end VG.Proof.MlDsa.AArch64.Verify

namespace VG.Proof.MlDsa.AArch64.Verify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem expA4_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VA p · (4*g)) (VA p · (4*g+4)) (expA4 P p g) := by
  unfold expA4
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s => VS p σ (4*g) j s) 4 0 (fun j _ hj => vslot_piece hF hg (by omega)))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (vcall4_piece hP hF hg)

theorem expAll_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (VA p · 0) (VA p · (p.k*p.ℓ)) (expAll P p) := by
  unfold expAll
  have hB : VPiece p S (VA p · 0) (VA p · (4*(p.k*p.ℓ/4))) (seqR (expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (VPiece.seqR (I := fun g σ s => VA p σ (4*g) s) (p.k*p.ℓ/4) 0 (fun g _ hg => expA4_vpiece hP hF (by omega)))
  refine VPiece.mono (VPiece.seq hB
    (VPiece.seqR (I := fun e σ s => VA p σ e s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he => expA_vpiece hP hF (by omega)))) (fun _ _ _ h => h) (fun _ _ _ h => ?_)
  have he : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [he] using h

theorem samples_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s => Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VB p) (samples P p) := by
  unfold samples sampled
  exact (copyRho_vpiece hF).seq ((expAll_vpiece hP hF).seq ((ballCall_vpiece hP hF).seq (ballTail_vpiece hF)))

end VG.Proof.MlDsa.AArch64.Verify
