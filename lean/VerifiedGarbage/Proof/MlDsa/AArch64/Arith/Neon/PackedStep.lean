import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Block

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_ldrq wp_strq VChg)
open VG.Spec.MlDsa (Poly Zq PolyIs zetas)

/-- Advance to the next eight coefficients after a packed butterfly batch. -/
theorem packedEnd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+32 ∧ s'.gpr .x5 = s.gpr .x5-1 ∧ s'.mem = s.mem) ∧
        Keep [.x2,.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun
  exact ⟨rfl,rfl⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem packedStep_ok {fP zP : Addr} {len u k : Nat} (hlen : len = 1 ∨ len = 2)
    (hu : u < 32) {F : Poly} (zi : Nat → Nat) (up : Bool)
    (hzi : ∀ e < 4, zi ((4/len)*u+e/len) = if up then k+e/len else k-e/len)
    {tab : Nat → Nat} (hzt : TabZ tab zt) (hb : up = false → 4/len ≤ k)
    (hbound : baseZ len up k+4 ≤ 256) {s : State}
    (hc : VConsts s) (hx : s.gpr .x2 = coeffAddr fP (8*u))
    (h3 : s.gpr .x3 = coeffAddr zP k)
    (hP : PolyIs s.mem fP (layF blk F len zi ((4/len)*u)))
    (ht : Tab tab s.mem zP 256) (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (.block (packedBody bf len up)) s fun s' =>
      PolyIs s'.mem fP (layF blk F len zi ((4/len)*(u+1))) ∧
      s'.gpr .x2 = coeffAddr fP (8*(u+1)) ∧
      s'.gpr .x3 = coeffAddr zP (if up then k+4/len else k-4/len) ∧
      s'.gpr .x5 = s.gpr .x5-1 ∧ Keep [.x2,.x3,.x5] s s' ∧ BInv fP s s' := by
  let G := layF blk F len zi ((4/len)*u)
  have j0 : 8*u+4 ≤ 256 := by omega
  have j1 : 8*u+4+4 ≤ 256 := by omega
  have a1 : coeffAddr fP (8*u)+16 = coeffAddr fP (8*u+4) := coeffAddr_add _ _ 4
  have r0 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j0⟩
  have r1 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u+4)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j1⟩
  unfold packedBody
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (by decide) (by rw [hx,BitVec.add_zero]) r0 fun s₁ h₁ =>
    wp_ldrq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₁.gpr,hx]; exact a1)
      (by rw [h₁.rd,h₁.wr]; exact r1) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  have hzcode : VG.Impl.MlDsa.AArch64.Arith.Neon.zetas len up = packedZetas len up := by
    rcases hlen with rfl | rfl <;> rfl
  rw [hzcode]
  refine WP.mono (packedZetas_ok (p := zP) (k := k) hzt len hlen up hb hbound
    (by rw [h₂.gpr,h₁.gpr]; exact h3) (by rw [h₂.mem,h₁.mem]; exact ht)
    (by rw [h₂.rd,h₂.wr,h₁.rd,h₁.wr]; exact hzp) (hc.chg (h₁.chg.trans h₂.chg)))
    fun s₃ ⟨lz,c₃,h33,hm₃,k₃,hv₃⟩ => ?_
  rw [WP.block_append_iff]
  have l6 : Coeffs (s₃.v .v6) (fun e => G[8*u+e]!) := by
    rw [hv₃ .v6 (by decide),h₂.get .v6,h₁.v]; exact coeffs_load hP j0
  have l7 : Coeffs (s₃.v .v7) (fun e => G[8*u+(4+e)]!) := by
    rw [hv₃ .v7 (by decide),h₂.v,h₁.mem]
    exact (coeffs_load hP j1).congr fun e _ => by dsimp only; rw [Nat.add_assoc]
  refine WP.mono (gather_ok len hlen l6 l7) fun s₄ ⟨h₄,la,lb⟩ => ?_
  rw [WP.block_append_iff]
  have z₄ : Zetas (s₄.v .v18) (fun e => zt (zetas (zi ((4/len)*u+e/len)))) := by
    rw [h₄.get .v18]
    exact lz.congr fun e he => by dsimp only; rw [hzi e he]
  refine WP.mono (hbf s₄ (c₃.chg h₄) _ _ _ la lb z₄) fun s₅ ⟨va,vb,h₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scatter_ok len hlen va vb) fun s₆ ⟨h₆,v6,v7⟩ => ?_
  have k06 : Keep [.x3] s s₆ := (((((h₁.keep.trans h₂.keep).trans k₃).trans h₄.keep).trans h₅.keep).trans h₆.keep).mono
  have g6 : s₆.gpr .x2 = coeffAddr fP (8*u) := by rw [k06.get .x2,hx]
  have m6 : s₆.mem = s.mem := by rw [h₆.mem,h₅.mem,h₄.mem,hm₃,h₂.mem,h₁.mem]
  refine wp_strq (by decide) (by rw [g6,BitVec.add_zero])
    (by rw [k06.wr]; exact ⟨_,hw,vector_contains _ j0⟩) fun s₇ h₇ =>
    wp_strq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₇.gpr,g6]; exact a1)
      (by rw [h₇.wr,k06.wr]; exact ⟨_,hw,vector_contains _ j1⟩) fun s₈ h₈ => ?_
  have mem₈ : s₈.mem = (s.mem.write (coeffAddr fP (8*u)) 16 (s₆.v .v6)).write
      (coeffAddr fP (8*u+4)) 16 (s₆.v .v7) := by rw [h₈.mem,h₇.mem,h₇.v,m6]
  have c₈ : VConsts s₈ := by
    have c₆ := ((c₃.chg h₄).chg h₅).chg h₆
    exact ⟨by rw [h₈.v,h₇.v]; exact c₆.q,by rw [h₈.v,h₇.v]; exact c₆.qi⟩
  refine WP.mono (packedEnd_ok s₈) fun s₉ ⟨⟨⟨hx9,hcnt9,hm9⟩,k₉⟩,hv9⟩ =>
    ⟨?_,?_,?_,?_,(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,
      ⟨(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,?_,
        ⟨by rw [hv9]; exact c₈.q,by rw [hv9]; exact c₈.qi⟩⟩⟩
  · rw [hm9,mem₈]
    refine polyIs_write2 hP j0 j1 (by omega) v6 v7 fun j hj => ?_
    rw [packed_batch_get hblk F zi len hlen hu hj]
    by_cases c1 : 8*u ≤ j ∧ j < 8*u+4
    · rw [ite_eq_left (by omega),ite_eq_left c1]
      simp only [G,Nat.add_assoc]
    · rw [ite_eq_right c1]
      by_cases c2 : 8*u+4 ≤ j ∧ j < 8*u+8
      · rw [ite_eq_left (by omega),ite_eq_left (by omega),show 4+(j-(8*u+4)) = j-8*u by omega]
        simp only [G,Nat.add_assoc]
      · rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  · rw [hx9,h₈.gpr,h₇.gpr,g6,show (32 : BitVec 64) = BitVec.ofNat 64 (4*8) from rfl,
      coeffAddr_add,show 8*u+8 = 8*(u+1) by omega]
  · rw [k₉.get .x3,h₈.gpr,h₇.gpr,h₆.gpr,h₅.gpr,h₄.gpr,h33]
  · rw [hcnt9,h₈.gpr,h₇.gpr,k06.get .x5]
  · rw [hm9,mem₈]; exact frame_write2 (Frame.refl _ _) j0 j1 _ _
end
end VG.Proof.MlDsa.AArch64.Arith.Neon
