import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def CPairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25,s.v (vreg i) = ofVDwords (chiWord A i) (chiWord B i)

theorem core2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block ((theta++rhoPi++chi).map Op.instr)) s fun t => Keep s t ∧ CPairs t A B := by
  refine WP.mono (ops_lanes (theta++rhoPi++chi) s) fun t ⟨ht,hl⟩ => ⟨ht,?_⟩
  have ha : ALanes (lane s 0) A := by
    intro i hi
    change vdword (s.v (vreg i)) 0 = _
    rw [hp i hi,vdword_ofVDwords_0,Proof.Sha3.getElem!_eq A hi]
  have hb : ALanes (lane s 1) B := by
    intro i hi
    change vdword (s.v (vreg i)) 1 = _
    rw [hp i hi,vdword_ofVDwords_1,Proof.Sha3.getElem!_eq B hi]
  have hca := core_math (lane s 0) A ha
  have hcb := core_math (lane s 1) B hb
  intro i hi
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    change lane t 0 (vreg i) = _
    rw [hl 0 (by decide)]
    exact hca i hi
  · rw [vdword_ofVDwords_1]
    change lane t 1 (vreg i) = _
    rw [hl 1 (by decide)]
    exact hcb i hi

theorem out_word (A : Spec.Sha3.State) (rc : BitVec 64) {i : Nat} (hi : i < 25) :
    (Proof.Sha3.outState A rc)[i]! = if i = 0 then chiWord A i ^^^ rc else chiWord A i := by
  rw [Proof.Sha3.getElem!_eq _ hi,chiWord_out A rc i hi]

theorem iota2_ok {s : State} {A B : Spec.Sha3.State} (hp : CPairs s A B) (rc : BitVec 64)
    (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun t => VChg allV s t ∧
      Pairs t (Proof.Sha3.outState A rc) (Proof.Sha3.outState B rc) := by
  unfold iota
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  rw [out_word A rc hi,out_word B rc hi]
  by_cases h0 : i = 0
  · subst i
    change t.v .v0 = ofVDwords (chiWord A 0 ^^^ rc) (chiWord B 0 ^^^ rc)
    rw [h2.v,h1.get .v0,h1.v,hc]
    change s.v .v0 ^^^ ofVDwords rc rc = _
    have hp0 : s.v .v0 = ofVDwords (chiWord A 0) (chiWord B 0) := hp 0 (by decide)
    rw [hp0,pair_xor]
  · rw [ite_eq_right h0,ite_eq_right h0,h2.get (vreg i) (by
      change ¬ vreg i = vreg 0
      rw [vreg_inj i (by omega) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem round2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ chi.map Op.instr ++ iota =
    constant (Spec.Sha3.RC r) ++ (theta++rhoPi++chi).map Op.instr ++ iota by
      simp only [List.map_append,List.append_assoc]]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s1 ⟨h1,hv1,hrc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s2 ⟨h2,hp2⟩ => ?_
  refine WP.mono (iota2_ok hp2 (Spec.Sha3.RC r) (by rw [h2.gpr,hrc,constantLow_RC r hr]))
    fun t ⟨h3,hpt⟩ => ⟨h1.trans (h2.core.trans (vchg_core h3)),?_⟩
  simpa only [Proof.Sha3.outState_eq] using hpt
end VG.Proof.Sha3.AArch64.Neon.Hw
