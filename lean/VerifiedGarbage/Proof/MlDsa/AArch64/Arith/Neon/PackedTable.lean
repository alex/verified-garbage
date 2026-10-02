import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layer

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep VChg wp_vop wp_ldrq)
open VG.Spec.MlDsa (q Zq)

set_option linter.unusedSimpArgs false

theorem vword_ext8 (v : BitVec 128) {e : Nat} (he : e < 4) :
    vword (((v++v) >>> (8*8)).extractLsb' 0 128) e = vword v ((e+2)%4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod,Nat.zero_add]
  all_goals rw [BitVec.getLsbD_append]
  all_goals simp +arith [hi]
  all_goals simp [show i ≤ 31 by omega,show i ≤ 63 by omega,show i ≤ 95 by omega,show i ≤ 127 by omega]

theorem table_vec {tab : Nat → Nat} {zt : Zq → Zq} (hzt : TabZ tab zt)
    {m : Mem} {p : Addr} (ht : Tab tab m p 256) {k : Nat} (hk : k+4 ≤ 256) :
    Zetas (m.read (coeffAddr p k) 16) (fun e => zt (Spec.MlDsa.zetas (k+e))) := fun e he => by
  rw [vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,ht (k+e) (by omega),
    BitVec.toNat_ofNat,hzt (k+e)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem zetaPerms_ok {s : State} {F : Nat → Zq} (len : Nat) (hlen : len = 1 ∨ len = 2)
    (up : Bool) (hz : Zetas (s.v .v18) F) :
    WP isa (.block (zetaPerms len up)) s fun s' => VChg [.v18] s s' ∧
      Zetas (s'.v .v18) (fun e => F (if up then e/len else 4/len-1-e/len)) := by
  rcases hlen with rfl | rfl <;> cases up
  · change WP isa (.block [.vop (.rev .rev64s .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (3-e)).val*2^32%q
    rw [h₂.v,vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_rev64s _ (by omega)]
    have hi : (if ((e+2)%4)%2 = 0 then (e+2)%4+1 else (e+2)%4-1) = 3-e := by split <;> omega
    rw [hi]; exact hz _ (by omega)
  · change WP isa (.block []) s _
    refine WP.block_nil_iff.mpr ⟨VChg.refl _ _,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s.v .v18) e).toNat = (F e).val*2^32%q
    exact hz e he
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (1-e/2)).val*2^32%q
    rw [h₂.v,vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ (by omega)]
    have hi : ((e+2)%4)/2 = 1-e/2 := by omega
    rw [hi]; exact hz _ (by omega)
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18)]) s _
    refine wp_vop (d := .v18) rfl fun s' h => WP.block_nil_iff.mpr ⟨h.chg,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s'.v .v18) e).toNat = (F (e/2)).val*2^32%q
    rw [h.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ he]; exact hz _ (by omega)

def baseZ (len : Nat) (up : Bool) (k : Nat) : Nat := if up then k else k-(4/len-1)

theorem coeffAddr_sub (p : Addr) (k j : Nat) (hj : j ≤ k) :
    coeffAddr p k - BitVec.ofNat 64 (4*j) = coeffAddr p (k-j) := by
  have h : coeffAddr p (k-j) + BitVec.ofNat 64 (4*j) = coeffAddr p k := by
    rw [coeffAddr_add,Nat.sub_add_cancel hj]
  rw [← h,BitVec.add_sub_cancel]

theorem moveZ_ok (N : Nat) (hN : N < 4096) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 N else .subImm .x .x3 .x3 N]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 N else s.gpr .x3-BitVec.ofNat 64 N) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [hN] <;> rfl

theorem zetaPre_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (h3 : s.gpr .x3 = coeffAddr p k) :
    WP isa (.block (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))])) s fun s' =>
      ((s'.gpr .x3 = coeffAddr p (baseZ len up k) ∧ s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · have hN : 4*(4/len-1) < 4096 := by rcases hlen with rfl | rfl <;> decide
    refine WP.mono (moveZ_ok _ hN false s) fun s' ⟨⟨⟨hx,hm⟩,hk⟩,hv⟩ => ⟨⟨⟨?_,hm⟩,hk⟩,hv⟩
    rw [hx,h3,coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
    rfl
  · exact WP.block_nil_iff.mpr ⟨⟨⟨h3,rfl⟩,Keep.refl _ _⟩,rfl⟩

theorem zetaPost_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 (16/len) else s.gpr .x3-4) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · exact moveZ_ok 4 (by decide) false s
  · exact moveZ_ok _ (by rcases hlen with rfl | rfl <;> decide) true s

theorem packedZetas_ok {tab : Nat → Nat} {zt : Zq → Zq} (hzt : TabZ tab zt)
    (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (hbound : baseZ len up k+4 ≤ 256)
    (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VConsts s) :
    WP isa (.block (packedZetas len up)) s fun s' =>
      Zetas (s'.v .v18) (fun e => zt (Spec.MlDsa.zetas (if up then k+e/len else k-e/len))) ∧
      VConsts s' ∧ s'.gpr .x3 = coeffAddr p (if up then k+4/len else k-4/len) ∧
      s'.mem = s.mem ∧ Keep [.x3] s s' ∧ (∀ v, v ≠ .v18 → s'.v v = s.v v) := by
  unfold packedZetas
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zetaPre_ok len hlen up hb h3) fun s₁ ⟨⟨⟨h31,hm1⟩,k1⟩,hv1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) (by rw [h31,BitVec.add_zero])
    (by rw [k1.rd,k1.wr]; exact ⟨_,hp,vector_contains _ hbound⟩) fun s₂ h2 => ?_
  have c2 : VConsts s₂ :=
    (⟨by rw [hv1]; exact hc.q,by rw [hv1]; exact hc.qi⟩ : VConsts s₁).chg h2.chg
  have z2 : Zetas (s₂.v .v18) (fun e => zt (Spec.MlDsa.zetas (baseZ len up k+e))) := by
    rw [h2.v,hm1]; exact table_vec hzt ht hbound
  rw [WP.block_append_iff]
  refine WP.mono (zetaPerms_ok len hlen up z2) fun s₃ ⟨h3v,z3⟩ => ?_
  refine WP.mono (zetaPost_ok len hlen up s₃) fun s₄ ⟨⟨⟨h34,hm4⟩,k4⟩,hv4⟩ =>
    ⟨?_,⟨by rw [hv4]; exact (c2.chg h3v).q,by rw [hv4]; exact (c2.chg h3v).qi⟩,?_,
      by rw [hm4,h3v.mem,h2.mem,hm1],(((k1.trans h2.keep).trans h3v.keep).trans k4).mono,
      by intro v hv; rw [hv4,h3v.get v (by simp [hv]),h2.get v hv,hv1]⟩
  · rw [hv4]
    exact z3.congr fun e he => by
      have hi : baseZ len up k+(if up then e/len else 4/len-1-e/len) =
          if up then k+e/len else k-e/len := by
        rcases hlen with rfl | rfl <;> cases up <;>
          simp only [baseZ,Bool.false_eq_true,ite_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub] at * <;>
          have hkk := hb (by trivial) <;> omega
      change (zt (Spec.MlDsa.zetas (baseZ len up k+(if up then e/len else 4/len-1-e/len)))).val*2^32%q = _
      rw [hi]
  · rw [h34,h3v.gpr,h2.gpr,h31]
    rcases hlen with rfl | rfl <;> cases up
    · simp only [baseZ,Bool.false_eq_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
      exact congrArg (coeffAddr p) (by omega)
    · simp only [baseZ,ite_true,Nat.div_one,Nat.reduceDiv]
      exact coeffAddr_add p k 4
    · simp only [baseZ,Bool.false_eq_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ (by have := hb rfl; omega)]
      exact congrArg (coeffAddr p) (by omega)
    · simp only [baseZ,ite_true,Nat.reduceDiv]
      exact coeffAddr_add p k 2

end VG.Proof.MlDsa.AArch64.Arith.Neon
