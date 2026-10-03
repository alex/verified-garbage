import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_ldrq wp_strq VChg)
open VG.Spec.MlDsa (q n Poly Zq PolyIs zetas)

/-- Pointer and counter updates leave all vector registers unchanged. -/
theorem bodyEnd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2 + 16 ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧ s'.mem = s.mem) ∧
        Keep [.x2,.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun
  exact ⟨rfl,rfl⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem step_ok {fP : Addr} {len st u k : Nat} (hl : 0 < len) (hl4 : len%4 = 0)
    (hs : st+2*len ≤ 256) (hu : 4*u+4 ≤ len) {G : Poly} {s : State}
    (hc : VConsts s) (hz : Zetas (s.v .v18) (fun _ => zt (zetas k)))
    (hx : s.gpr .x2 = coeffAddr fP (st+4*u))
    (hP : PolyIs s.mem fP (blk G len k st (4*u))) (hw : pR fP ∈ s.wr) :
    WP isa (.block (body bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (4*(u+1))) ∧
      Frame [pR fP] s.mem s'.mem ∧ VConsts s' ∧ s'.v .v18 = s.v .v18 ∧
      s'.gpr .x2 = coeffAddr fP (st+4*(u+1)) ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧
      Keep [.x2,.x5] s s' := by
  have j0 : st+4*u+4 ≤ 256 := by omega
  have j1 : st+4*u+len+4 ≤ 256 := by omega
  have off : 4*len%16 = 0 ∧ 4*len < 4096*16 := ⟨by omega, by omega⟩
  have a1 : coeffAddr fP (st+4*u) + BitVec.ofNat 64 (4*len) = coeffAddr fP (st+4*u+len) := coeffAddr_add _ _ _
  have r0 : InRegions (s.rd++s.wr) (coeffAddr fP (st+4*u)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j0⟩
  have r1 : InRegions (s.rd++s.wr) (coeffAddr fP (st+4*u+len)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j1⟩
  unfold body
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) (by rw [hx, BitVec.add_zero]) r0 fun s₁ h₁ =>
    wp_ldrq off (by rw [h₁.gpr, hx, a1])
      (by rw [h₁.rd,h₁.wr]; exact r1) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  have cc := hc.chg (h₁.chg.trans h₂.chg)
  have zz : Zetas (s₂.v .v18) (fun _ => zt (zetas k)) := by rw [h₂.get .v18,h₁.get .v18]; exact hz
  have l0 : Coeffs (s₂.v .v0) (fun e => (blk G len k st (4*u))[st+4*u+e]!) := by
    rw [h₂.get .v0,h₁.v]; exact coeffs_load hP j0
  have l1 : Coeffs (s₂.v .v1) (fun e => (blk G len k st (4*u))[st+4*u+len+e]!) := by
    rw [h₂.v,h₁.mem]; exact coeffs_load hP j1
  refine WP.mono (hbf s₂ cc _ _ _ l0 l1 zz) fun s₃ ⟨la,lb,h₃⟩ => ?_
  have g₃ : s₃.gpr = s.gpr := h₃.gpr.trans (h₂.gpr.trans h₁.gpr)
  have m₃ : s₃.mem = s.mem := h₃.mem.trans (h₂.mem.trans h₁.mem)
  have rd₃ : s₃.rd = s.rd := h₃.rd.trans (h₂.rd.trans h₁.rd)
  have wr₃ : s₃.wr = s.wr := h₃.wr.trans (h₂.wr.trans h₁.wr)
  refine wp_strq (by decide) (by rw [g₃,hx,BitVec.add_zero])
    (by rw [wr₃]; exact ⟨_,hw,vector_contains _ j0⟩) fun s₄ h₄ =>
    wp_strq off (by rw [h₄.gpr,g₃,hx,a1])
      (by rw [h₄.wr,wr₃]; exact ⟨_,hw,vector_contains _ j1⟩) fun s₅ h₅ => ?_
  have mem₅ : s₅.mem = ((s.mem.write (coeffAddr fP (st+4*u)) 16 (s₃.v .v0)).write
      (coeffAddr fP (st+4*u+len)) 16 (s₃.v .v5)) := by
    rw [h₅.mem,h₄.mem,h₄.v,m₃]
  have c₅ : VConsts s₅ := by
    have c₃ := cc.chg h₃
    exact ⟨by rw [h₅.v,h₄.v]; exact c₃.q, by rw [h₅.v,h₄.v]; exact c₃.qi⟩
  refine WP.mono (bodyEnd_ok s₅) fun s₆ ⟨⟨⟨hx6,hcnt6,hm6⟩,h₆⟩,hv6⟩ =>
    ⟨?_, ?_, ⟨by rw [hv6]; exact c₅.q, by rw [hv6]; exact c₅.qi⟩,
      by rw [hv6,h₅.v,h₄.v,h₃.get .v18,h₂.get .v18,h₁.get .v18], ?_, ?_,
      (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆).mono⟩
  · rw [hm6,mem₅]
    refine polyIs_write2 hP j0 j1 (by omega) la lb fun i hi => ?_
    rw [show 4*(u+1) = 4*u+4 by omega,hblk.add,hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st+4*u ≤ i ∧ i < st+4*u+4
    · rw [ite_eq_left c1,ite_eq_left c1,
        show st+4*u+(i-(st+4*u)) = i by omega,
        show st+4*u+len+(i-(st+4*u)) = i+len by omega]
    · rw [ite_eq_right c1,ite_eq_right c1]
      by_cases c2 : st+4*u+len ≤ i ∧ i < st+4*u+len+4
      · rw [ite_eq_left c2,ite_eq_left (by omega),
          show st+4*u+(i-(st+4*u+len)) = i-len by omega,
          show st+4*u+len+(i-(st+4*u+len)) = i by omega]
      · rw [ite_eq_right c2,ite_eq_right (by omega)]
  · rw [hm6,mem₅]; exact frame_write2 (Frame.refl _ _) j0 j1 _ _
  · rw [hx6,h₅.gpr,h₄.gpr,g₃,hx,show (16 : BitVec 64) = BitVec.ofNat 64 (4*4) from rfl,
      coeffAddr_add,show st+4*u+4 = st+4*(u+1) by omega]
  · rw [hcnt6,h₅.gpr,h₄.gpr,g₃]
end
end VG.Proof.MlDsa.AArch64.Arith.Neon
