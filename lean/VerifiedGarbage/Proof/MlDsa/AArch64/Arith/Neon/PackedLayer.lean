import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layer

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- A complete length-one or length-two NTT layer, processed eight coefficients at a time. -/
theorem layer_packed_ok {fP zP : Addr} {len : Nat} (hlen : len = 1 ∨ len = 2)
    {tab : Nat → Nat} (hzt : TabZ tab zt) (up : Bool) (zi kz : Nat → Nat)
    (hk0 : kz 0 = firstZ len up)
    (hzi : ∀ u < 32, ∀ e < 4, zi ((4/len)*u+e/len) = if up then kz u+e/len else kz u-e/len)
    (hb : ∀ u < 32, up = false → 4/len ≤ kz u)
    (hbound : ∀ u < 32, baseZ len up (kz u)+4 ≤ 256)
    (hnext : ∀ u < 32, (if up then kz u+4/len else kz u-4/len) = kz (u+1))
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab tab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bf len up) s fun s' =>
      PolyIs s'.mem fP (layF blk F len zi (128/len)) ∧ BInv fP s s' := by
  have hf : 4*firstZ len up < 4096 := by
    rcases hlen with rfl | rfl <;> cases up <;> decide
  have hcov : (4/len)*32 = 128/len := by rcases hlen with rfl | rfl <;> decide
  have hsmall : len < 4 := by rcases hlen with rfl | rfl <;> decide
  unfold layer
  rw [ite_eq_left hsmall]
  refine WP.seq (WP.mono (preLayer_ok len up hf s) fun s₁ ⟨⟨⟨hx2,hx3,hm1⟩,k1⟩,hv1⟩ => ?_)
  refine WP.seq (WP.mono (counter5_ok 32 (by decide) s₁)
    fun s₂ ⟨⟨⟨hcnt,hm2⟩,k2⟩,hv2⟩ => ?_)
  have c2 : VConsts s₂ := ⟨by rw [hv2,hv1]; exact hc.q,by rw [hv2,hv1]; exact hc.qi⟩
  refine WP.mono (wp_countdown (cnt := .x5) (N := 32) (by decide) (by decide)
    (fun u s' => PolyIs s'.mem fP (layF blk F len zi ((4/len)*u)) ∧
      s'.gpr .x2 = coeffAddr fP (8*u) ∧ s'.gpr .x3 = coeffAddr zP (kz u) ∧
      BInv fP s₂ s' ∧ Tab tab s'.mem zP 256)
    (fun u hu s' ⟨hp,hx2',hx3',hi,ht'⟩ _ => ?_)
    ⟨by rw [hm2,hm1]; exact hP,
      by rw [k2.get .x2,hx2,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],
      by rw [k2.get .x3,hx3,h1,hk0],BInv.refl c2,by rw [hm2,hm1]; exact ht⟩ hcnt)
    fun s' ⟨hp,_,_,hi,_⟩ =>
      ⟨by simpa only [hcov] using hp,⟨((k1.trans k2).trans hi.keep).mono,
        by simpa only [hm2,hm1] using hi.frame,hi.consts⟩⟩
  refine WP.mono (packedStep_ok hbf hblk hlen hu zi up (hzi u hu) hzt (hb u hu)
    (hbound u hu) hi.consts hx2' hx3' hp ht'
    (by rw [hi.keep.wr,k2.wr,k1.wr]; exact hw)
    (by rw [hi.keep.rd,hi.keep.wr,k2.rd,k2.wr,k1.rd,k1.wr]; exact hzp))
    fun s'' ⟨hp',hx2'',hx3'',hc'',_,hi'⟩ =>
      ⟨⟨hp',hx2'',by rw [hx3'',hnext u hu],hi.trans hi',
        ht'.frame hi'.frame (by simpa using hd) (by decide)⟩,hc''⟩
end
end VG.Proof.MlDsa.AArch64.Arith.Neon
