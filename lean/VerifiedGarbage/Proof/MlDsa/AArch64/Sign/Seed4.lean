import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Call4
/-! Signing matrix expansion: four seeds, with the earlier matrix and caller state preserved. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def seedCopy4 (j : Nat) : List Instr := lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0

theorem copySeed4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oRS) 32 = true)
    (hdst : inB wbs (sc (oRS4+34*j)) 32 = true)
    (hsep : sepB (rbs++wbs) (sc oRS) 32 (sc (oRS4+34*j)) 32 = true) :
    WP isa (.block (seedCopy4 j)) s fun t =>
      PPostB S s t [(sc (oRS4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oRS4+34*j))) 32 = bytesAt s.mem (pa s (sc oRS)) 32 := by
  unfold seedCopy4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oRS4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oRS,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oRS),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oRS4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oRS4+34*j))) (sb := .x28) (db := .x10) (so := oRS) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oRS),32⟩ : Region).Disjoint ⟨pa s (sc (oRS4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]


end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

structure AS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia : IA p D σ e s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oRS4+34*k))) 34 = seedE p σ (e+k)

def slotChk (p : Params) (e j : Nat) : Bool :=
  let ws : List (Ptr × Nat) := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)]
  inB (sgB p) (sc oRS) 32 && inB (sgW p) (sc (oRS4+34*j)) 32 &&
    sepB (sgB p) (sc oRS) 32 (sc (oRS4+34*j)) 32 && stChk p ws &&
    keepB (sgB p) ws (sc oRS) 32 && famChk (sgB p) ws (aBase p) e &&
    inB (sgW p) (sc (oRS4+34*j+32)) 1 && inB (sgW p) (sc (oRS4+34*j+33)) 1 &&
    keepB (sgB p) [(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j+32)) 1 &&
    keepB (sgB p) [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j)) 32 &&
    (List.range j).all (fun k => keepB (sgB p) ws (sc (oRS4+34*k)) 34)

theorem slotChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ e < p.k*p.ℓ,∀ j < 4,slotChk p e j = true := by
  decide +kernel

theorem IA.keep {p : Params} {D : Nat} {σ s t : State} {e : Nat} (h : IA p D σ e s)
    {ws : List (Ptr × Nat)} (hp : PPostB D s t ws) (hc : stChk p ws = true)
    (hr : keepB (sgB p) ws (sc oRS) 32 = true) (hf : famChk (sgB p) ws (aBase p) e = true)
    (h24 : t.gpr .x24 = s.gpr .x24) : IA p D σ e t :=
  ⟨h.st.step hp hc,(h.st.lay.keepBytes hp hr).trans h.rs,h24 ▸ h.r01,
    fun ht => let ⟨ok,fam⟩ := h.ok (h24 ▸ ht); ⟨ok,Fam.keep h.st.lay hp hf fam⟩,
    fun ht => h.bad (h24 ▸ ht)⟩

theorem slot4_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj : j < 4)
    (hc : slotChk p e j = true) {s : State} (h : AS p D σ e j s) :
    WP isa (seedSlot4 p e j) s fun t => AS p D σ e (j+1) t ∧ t.gpr .x24 = s.gpr .x24 := by
  simp only [slotChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨csrc,cdst⟩,csep⟩,cst⟩,crs⟩,cfam⟩,cw1⟩,cw2⟩,ck12⟩,ck32⟩,ckprev⟩ := hc
  have L := h.ia.st.lay
  unfold seedSlot4
  change WP isa (.seq (.block (seedCopy4 j)) _) s _
  refine WP.seq (WP.mono (copySeed4_ok L csrc cdst csep) fun s1 ⟨hP1,k1,b1⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (L.post hP1) (p := sc (oRS4+34*j+32)) (v := (e+j)%p.ℓ)
    (by dsimp only [oRS4]; omega) cw1 (by change Reg.x28 ∈ bases; decide)) fun s2 ⟨hP2,k2,m2⟩ => ?_
  refine WP.mono (setB_ok ((L.post hP1).post hP2) (p := sc (oRS4+34*j+33)) (v := (e+j)/p.ℓ)
    (by dsimp only [oRS4]; omega) cw2 (by change Reg.x28 ∈ bases; decide)) fun t ⟨hP3,k3,m3⟩ => ?_
  have hp12 := PPostB.trans hP1 hP2 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1)])
    (by simp [sc,bases]) (by simp) (by simp)
  have hp := PPostB.trans hp12 hP3 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
    (by simp [sc,bases]) (by simp) (by simp)
  have h24 : t.gpr .x24 = s.gpr .x24 := by rw [k3.get .x24,k2.get .x24,k1.get .x24]
  refine ⟨⟨h.ia.keep hp cst crs cfam h24,fun k hk => ?_⟩,h24⟩
  by_cases heq : k = j
  · subst k
    have hrho : bytesAt t.mem (pa t (sc (oRS4+34*j))) 32 = rhoOf p σ := by
      have hp23 := PPostB.trans hP2 hP3 (ws := [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
        (by simp [sc,bases]) (by simp) (by simp)
      rw [(L.post hP1).keepBytes hp23 ck32,hP1.pa (by change Reg.x28 ∈ bases; decide),b1,h.ia.rs]
    refine seed34 hrho ?_ ?_
    · rw [pa_sc_add,((L.post hP1).post hP2).keepBytes hP3 ck12,m2,hP2.pa (by change Reg.x28 ∈ bases; decide)]
      exact bytes1_write _ _ _
    · rw [pa_sc_add,m3,hP3.pa (by change Reg.x28 ∈ bases; decide)]
      exact bytes1_write _ _ _
  · rw [L.keepBytes hp (ckprev k (by omega))]
    exact h.done k (by omega)

end VG.Proof.MlDsa.AArch64.Sign
