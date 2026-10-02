import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Seed4
import VerifiedGarbage.Proof.MlDsa.Sample.Rej4

/-! Signing matrix expansion in batches of four: sampler outcomes, bounded failure, and the single-stream remainder. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem aseeds_eq {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oRS4)) k = seedE p σ (e+k) := by
  unfold seed4
  rw [pa_sc_add]
  exact h.done k hk

theorem rej4Call_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {s : State} (L : Lay D (sgR p) (sgW p) s)
    {seed a ss : Ptr} (hc : rej4Chk (sgR p) (sgW p) seed a ss = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (rej4Args seed a ss)) s fun t =>
      PPostB D s t [(a,4096),(ss,8192)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced t.mem (poly4 (pa s a) k)) ∧
      (((t.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt t.mem (poly4 (pa s a) k))) ∨
        ((t.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s seed) k)).isSome) := by
  have hc' := hc
  simp only [rej4Chk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,c4,c5,c6,_,_⟩ := hc'
  refine WP.mono (callAtK_ok L.s64 (hP.rej4.withPost hP.rej4Max) (rej4_args L.ok c4 c5 c6)
    (by simp only [List.map_cons,List.map_nil]; decide) (fun s1 h1 => rej4_pre L hc h1) (rej4_cov L hc).1
    (rej4_cov L hc).2) fun t ⟨hp,s1,h1,hq,hx⟩ => ⟨hp.b,hp.cs .x24 (by decide) (by decide),?_⟩
  sig_post [rejNTT4Contract,rejNTT4Sig,AArch64.abi,AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  simp only [State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),Args.r0 h1,Args.mem h1,Arg.val] at hx
  exact ⟨hq.1,hq.2,hx⟩

def batchChk (p : Params) (g : Nat) : Bool :=
  let a := pS (aBase p+4*g)
  let ws : List (Ptr × Nat) := [(a,4096),(sc (oR4 p),8192)]
  rej4Chk (sgR p) (sgW p) (sc oRS4) a (sc (oR4 p)) && stChk p ws && stChk p [] &&
    keepB (sgB p) ws (sc oRS) 32 && famChk (sgB p) ws (aBase p) (4*g)

theorem batchChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ g < p.k*p.ℓ/4,batchChk p g = true := by decide +kernel

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (pS e)) k = pa s (pS (e+k)) := by
  unfold poly4
  rw [pa_sc_add]
  rw [show oP e+1024*k = oP (e+k) by simp only [oP]; omega]

theorem batch_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : batchChk p g = true) {s : State} (h : AS p D σ (4*g) 4 s) :
    WP isa (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      (rej4Args (sc oRS4) (pS (aBase p+4*g)) (sc (oR4 p)))) (.block and24)) s
      (IA p D σ (4*g+4)) := by
  simp only [batchChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨cr,cst⟩,c0⟩,crs⟩,cfam⟩ := hc
  refine WP.seq (WP.mono (rej4Call_ok hP h.ia.st.lay cr) fun s1 ⟨hp,h24,hred,hout,hmax⟩ => ?_)
  have S1 := h.ia.st.step hp cst
  refine WP.mono (and24_ok s1) fun t ⟨kt,et⟩ => ?_
  have hpt : PPostB D s1 t [] := postB24 kt _
  have hr : (s1.gpr .x0).setWidth 32 = 1 ∨ (s1.gpr .x0).setWidth 32 = 0 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inl h1,.inr h0]
  have et' : t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s1.gpr .x0).setWidth 32) := by rw [et,h24]
  refine ⟨S1.step hpt c0,by rw [kt.mem,hpt.pa (by decide),h.ia.st.lay.keepBytes hp crs]; exact h.ia.rs,
    ?_,fun ht => ?_,fun ht => ?_⟩
  · rw [et']
    rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] <;> decide
  · have hs : s.gpr .x24 = 1 ∧ (s1.gpr .x0).setWidth 32 = 1 := by
      rw [et'] at ht
      rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] at ht <;>
        first | exact ⟨e0,e1⟩ | exact absurd ht (by decide)
    obtain ⟨ok,fam⟩ := h.ia.ok hs.1
    have fm := Fam.of_eq kt.mem (hpt.bs _ (by decide)) (Fam.keep h.ia.st.lay hp cfam fam)
    refine ⟨fun e' he' => ?_,fun e' he' => ?_⟩
    · by_cases hlt : e' < 4*g
      · exact ok e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
        rw [← aseeds_eq h (by omega)]; exact hmax hs.2 k (by omega)
    · by_cases hlt : e' < 4*g
      · exact fm e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
        have hk : k < 4 := by omega
        have hm := hmax hs.2 k hk
        have hv : polyAt s1.mem (poly4 (pa s (pS (aBase p+4*g))) k) = aVal p σ (4*g+k) := by
          obtain ⟨_,hb⟩ | ⟨h0,_⟩ := hout
          · have hv := rej_val (.inl ⟨hs.2,hb k hk⟩) hs.2 hm
            rw [aseeds_eq h hk] at hv
            exact hv
          · rw [hs.2] at h0; cases h0
        show PolyIs t.mem (pa t (pS (aBase p+(4*g+k)))) (aVal p σ (4*g+k))
        rw [kt.mem,hpt.pa (by change Reg.x28 ∈ bases; decide),hp.pa (by change Reg.x28 ∈ bases; decide),← Nat.add_assoc,← pa_poly4]
        exact ⟨hred hs.2 k hk,hv⟩
  · rw [et'] at ht
    rcases h.ia.r01 with e0 | e0
    · obtain ⟨e',he',hn⟩ := h.ia.bad e0; exact ⟨e',by omega,hn⟩
    · rcases hr with e1 | e1
      · rw [e0,e1] at ht; exact absurd ht (by decide)
      · rcases hout with ⟨h1,_⟩ | ⟨_,k,hk,hn⟩
        · exact absurd (e1.symm.trans h1) (by decide)
        · exact ⟨4*g+k,by omega,by rw [← aseeds_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem sample4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hb : batchChk p g = true) (hs : ∀ j < 4,slotChk p (4*g) j = true) {s : State} (h : IA p D σ (4*g) s) :
    WP isa (sample4 P p g) s (IA p D σ (4*g+4)) := by
  unfold sample4
  refine WP.seq (WP.mono (seqR_ok (I := AS p D σ (4*g)) 4 0
    (fun j _ hj s h => WP.mono (slot4_ok (by omega) (hs j (by omega)) h) fun _ ht => ht.1)
    s ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩) fun t ht => ?_)
  exact batch_ok hP hb (by simpa using ht)

theorem sampleAll_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p)
    (hc : aChk p = true) {σ s : State} (h : IA p D σ 0 s) :
    WP isa (sampleAll P p) s (IA p D σ (p.k*p.ℓ)) := by
  have hp : p ∈ [mlDsa44,mlDsa65,mlDsa87] := by rcases h3 with rfl | rfl | rfl <;> simp
  have he : ∀ e < p.k*p.ℓ,eChk p e = true := by
    simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc
    exact hc.1.1.1
  unfold sampleAll
  refine WP.seq (WP.mono (seqR_ok (I := fun g => IA p D σ (4*g)) (p.k*p.ℓ/4) 0
    (fun g _ hg s h => sample4_ok hP (batchChk_ok p hp g (by omega))
      (fun j hj => slotChk_ok p hp (4*g) (by omega) j hj) h) s h) fun t ht => ?_)
  have htail := seqR_ok (I := IA p D σ) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
    (fun e _ he' s h => sampleE_ok hP (he e (by omega)) h) t (by simpa only [Nat.zero_add] using ht)
  have eqn : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [eqn] using htail

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .x24 = 1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s (IA p D σ (p.k*p.ℓ)) := by
  have hc' := hc
  simp only [aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨_,hcp⟩,hst⟩,hsk⟩ := hc'
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1,hcs1,hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24,h15]
  exact sampleAll_ok hP h3 hc ⟨S1,by rw [hP1.pa (by decide),hb,rhoOf,← hs.sk,VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15,fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _),fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩

end VG.Proof.MlDsa.AArch64.Sign
