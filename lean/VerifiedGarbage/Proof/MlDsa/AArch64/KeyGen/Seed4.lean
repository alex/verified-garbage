import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa (Params Poly IPoly Reduced PolyIs polyAt poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

theorem copySeed4_generic {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oSA) 32 = true)
    (hdst : inB wbs (sc (oSA4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oSA) 32 (sc (oSA4+34*j)) 32 = true) :
    WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  unfold copySeed4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oSA4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oSA,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oSA),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oSA4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oSA4+34*j))) (sb := .x28) (db := .x10) (so := oSA) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oSA),32⟩ : Region).Disjoint ⟨pa s (sc (oSA4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

theorem copySeed4_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State} (L : Lay S kgR (kgW p) s)
    {j : Nat} (hj : j < 4) : WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  exact copySeed4_generic L (by lay) (by lay) (by lay)

structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : KSamp p σ e 0 s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 =
    seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ)

theorem slot_ok {P : Params} (hF : PFacts P) {S : Nat} {σ : State} (hp : kgPre P S σ)
    {e j : Nat} (he : e+4 ≤ P.k*P.ℓ) (hj : j < 4) {s : State} (h : GS P σ e j s) :
    WP isa (seedSlot4 P e j) s (GS P σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq P
  have L := h.ks.k1.kc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_ok hF L hj) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.ks.keep hF hp hP1 (by unfold k1Chk kcChk; lay)
    (fun k hk => by lay) (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk1.get .x24)
  have L1 := h1.k1.kc.lay hF hp
  unfold setSR
  refine WP.mono (setTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%P.ℓ) (b := (e+j)/P.ℓ)
    (by dsimp only [oSA4]; omega) (by lay) (by lay)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by unfold k1Chk kcChk; lay) (fun k hk => by lay)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by lay),sc_pa hP2,sc_pa hP1,hb1,h.ks.k1.sa,
      sc_add,← sc_pa hP1,hb2,Proof.MlDsa.KeyGen.seedA_eq]
  · rw [L1.keepBytes hP2 (by lay),L.keepBytes hP1 (by lay)]
    exact h.done k (by omega)
end VG.Proof.MlDsa.AArch64.KeyGen

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem slot_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs [.x28]) (seedSlot4 p e j) (.seq (Taint.ofRegs [.x28,.x10]) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 copySeed4 lea
  rw [VG.Proof.MlDsa.KeyGen.ifp (by dsimp only [oSA4]; omega : oSA4+34*j < 4096)]
  with_unfolding_all rfl

theorem slot_piece {p : Params} (hF : PFacts p) {S e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) :
    Piece p S (GS p · e j) (GS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => slot_ok hF hp he hj h,
    rel_of (Q := Two p S) (taintRel [.x28] (fun _ _ h => Two.x28 h) (slot_taint p e hj))
      fun _ _ _ _ hp hp' hq h h' => kc_two hF hp hp' hq h.ks.k1.kc h'.ks.k1.kc⟩
end VG.Proof.MlDsa.AArch64.KeyGen
