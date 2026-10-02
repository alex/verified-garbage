import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseACT

/-! Four-way matrix expansion leaks only the public matrix seed. The batch return is public before signing branches on it. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem postDepQ {Q R T : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (htr : RelCT isa Q c R) (hw : ∀ x y,Q x y → (WP isa c x (F x)) ∧ (WP isa c y (F y)))
    (hq : ∀ x y x' y',Q x y → F x x' → F y y' → R x' y' → T x' y') : RelCT isa Q c T := by
  intro x y tx ty x' y' hp ex ey
  obtain ⟨ht,hr⟩ := htr x y tx ty x' y' hp ex ey
  obtain ⟨hx,hy⟩ := hw x y hp
  obtain ⟨_,u,eu,hu⟩ := hx
  obtain ⟨_,v,ev,hv⟩ := hy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨ht,hq x y x' y' hp hu hv hr⟩

theorem slot4_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs bases) (seedSlot4 p e j) (.seq (Taint.ofRegs (.x10::bases)) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 lea
  rw [ifp (by dsimp only [oRS4]; omega : oRS4+34*j < 4096)]
  with_unfolding_all rfl

theorem slot4_tr {p : Params} {D e j : Nat} (hj : j < 4) (hc : slotChk p e j = true) :
    RelCT isa (RR p D (AS p D · e j) fun x y => x.gpr .x24 = y.gpr .x24)
      (seedSlot4 p e j) (RR p D (AS p D · e (j+1)) fun x y => x.gpr .x24 = y.gpr .x24) :=
  stepRR (F := fun s t => t.gpr .x24 = s.gpr .x24) (fun _ _ _ h => slot4_ok hj hc h)
    (lrel_tr (fun _ _ h => h.lrel fun _ _ h => h.ia.st) (slot4_taint p e hj))
    fun _ _ _ _ h hx hy _ => by rw [hx,hy,h.2]

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P+BitVec.ofNat 64 34) 34 ++
    bytesAt m (P+BitVec.ofNat 64 68) 34 ++ bytesAt m (P+BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34+102 from rfl,VG.Proof.MlKem.bytesAt_add,show 102=34+68 from rfl,VG.Proof.MlKem.bytesAt_add,
    show 68=34+34 from rfl,VG.Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc,← BitVec.ofNat_add,List.append_assoc,Nat.reduceAdd]

theorem AS.seeds {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 4 s) :
    bytesAt s.mem (pa s (sc oRS4)) 136 = seedE p σ (e+0) ++ seedE p σ (e+1) ++ seedE p σ (e+2) ++ seedE p σ (e+3) := by
  have b : ∀ k < 4,bytesAt s.mem (pa s (sc oRS4)+BitVec.ofNat 64 (34*k)) 34 = seedE p σ (e+k) :=
    fun k hk => aseeds_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34*0=0 from rfl,VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [bytes136,b0,b 1 (by decide),b 2 (by decide),b 3 (by decide)]

theorem batch_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat} (hc : batchChk p g = true) :
    RelCT isa (RR p D (AS p D · (4*g) 4) fun x y => x.gpr .x24 = y.gpr .x24)
      (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (rej4Args (sc oRS4) (pS (aBase p+4*g)) (sc (oR4 p)))) (.block and24))
      (RA p D (4*g+4)) := by
  have hc' := hc
  simp only [batchChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨cr,_⟩,_⟩,_⟩,_⟩ := hc'
  refine stepRR (F := fun _ _ => True) (fun _ _ _ h => WP.mono (batch_ok hP hc h) fun _ ht => ⟨ht,trivial⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have calltr : RelCT isa (RR p D (AS p D · (4*g) 4) fun x y => x.gpr .x24 = y.gpr .x24)
      (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (rej4Args (sc oRS4) (pS (aBase p+4*g)) (sc (oR4 p))))
      (fun x y => LRel D (sgR p) (sgW p) x y ∧ x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) := by
    refine postDepQ (fun x y t1 t2 x' y' h e1 e2 =>
      rej4AtK_trRet hP.rej4 hP.rej4Ret (h.lrel fun _ _ h => h.ia.st).lx.ok cr ?_ x y t1 t2 x' y' h e1 e2)
      (F := fun s t => PPostB D s t [(pS (aBase p+4*g),4096),(sc (oR4 p),8192)] ∧ t.gpr .x24 = s.gpr .x24)
      ?_ ?_
    · intro x y h
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨L.lx,L.ly,?_,L.same⟩
      obtain ⟨⟨σ1,σ2,_,_,pub,h1,h2⟩,_⟩ := h
      rw [h1.seeds,h2.seeds]
      simp only [seedE,pub_rho pub]
    · intro x y h
      obtain ⟨⟨σ1,σ2,_,_,_,h1,h2⟩,_⟩ := h
      exact ⟨WP.mono (rej4Call_ok hP h1.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩),
        WP.mono (rej4Call_ok hP h2.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩)⟩
    · intro x y x' y' h hx hy hr
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨⟨L.lx.post hx.1,L.ly.post hy.1,fun r hr => ?_,?_⟩,by rw [hx.2,hy.2,h.2],hr⟩
      · rw [hx.1.bs r hr,hy.1.bs r hr]; exact L.regs r hr
      · rw [hx.1.sp,hy.1.sp]; exact L.sp
  refine RelCT.seq calltr (RelCT.postDep (lrel_tr (fun _ _ h => h.1) (by taint_decide))
    (F := fun s t => t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
    (fun x y _ => ⟨WP.mono (and24_ok x) (fun _ h => h.2),WP.mono (and24_ok y) (fun _ h => h.2)⟩)
    fun x y x' y' h hx hy => by rw [hx,hy,h.2.1,h.2.2])

theorem sample4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat}
    (hb : batchChk p g = true) (hs : ∀ j < 4,slotChk p (4*g) j = true) :
    RelCT isa (RA p D (4*g)) (sample4 P p g) (RA p D (4*g+4)) := by
  unfold sample4
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun j => RR p D (AS p D · (4*g) j) fun x y => x.gpr .x24 = y.gpr .x24) 4 0
    (fun j _ hj => slot4_tr (by omega) (hs j (by omega)))) ?_ (fun _ _ h => by simpa using h)) (batch_tr hP hb)
  exact fun x y h => h.mono (fun _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩) (fun h => h)

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (hc : aChk p = true) :
    RelCT isa (RR p D (fun σ s => St p D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.expandA P p) (RA p D (p.k * p.ℓ)) := by
  have hp : p ∈ [mlDsa44,mlDsa65,mlDsa87] := by rcases h3 with rfl | rfl | rfl <;> simp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine RelCT.seq (R := RA p D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA p D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · unfold sampleAll
    have hB : RelCT isa (RA p D 0) (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (RA p D (4*(p.k*p.ℓ/4))) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (R := fun g => RA p D (4*g)) (p.k*p.ℓ/4) 0 (fun g _ hg =>
          sample4_tr hP (batchChk_ok p hp g (by omega)) (fun j hj => slotChk_ok p hp (4*g) (by omega) j hj)))
    have htail := seqR_tr (R := fun e => RA p D e) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he' => sampleE_tr hP (he e (by omega)))
    have eqn : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
    simpa only [eqn] using RelCT.seq hB htail

end VG.Proof.MlDsa.AArch64.Sign
