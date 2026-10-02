import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Block

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown imm16)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

def firstZ (len : Nat) (up : Bool) : Nat := if up then 128/len else 256/len-1

theorem preLayer_ok (len : Nat) (up : Bool) (hk : 4*firstZ len up < 4096) (s : State) :
    WP isa (.block [Impl.MlKem.AArch64.mov .x2 .x0,
      .addImm .x .x3 .x1 (4*firstZ len up)]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x0 ∧ s'.gpr .x3 = coeffAddr (s.gpr .x1) (firstZ len up) ∧
        s'.mem = s.mem) ∧ Keep [.x2,.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [Impl.MlKem.AArch64.mov,hk]

theorem counter4_ok (N : Nat) (hN : N < 65536) (s : State) :
    WP isa (.block [.movz .x .x4 (BitVec.ofNat 16 N) 0]) s fun s' =>
      ((s'.gpr .x4 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.x4] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hN]

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem layer_large_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ [4,8,16,32,64,128])
    {tab : Nat → Nat} (hzt : TabZ tab zt) (up : Bool) (zi : Nat → Nat)
    (hzi0 : zi 0 = firstZ len up) (hzi : ∀ c < 128/len, zi c < 256)
    (hstep : ∀ c < 128/len, (if up then coeffAddr zP (zi c)+4 else coeffAddr zP (zi c)-4) =
      coeffAddr zP (zi (c+1))) {F : Poly} {s : State}
    (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP) (hc : VConsts s)
    (hP : PolyIs s.mem fP F) (ht : Tab tab s.mem zP 256) (hw : pR fP ∈ s.wr)
    (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bf len up) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128/len)) ∧ BInv fP s s' := by
  have hfacts : 4 ≤ len ∧ len%4 = 0 ∧ len ≤ 128 ∧ 2*len*(128/len) = 256 ∧
      0 < 128/len ∧ 128/len ≤ 32 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h4,hl4,hl,hcov,hN0,hN⟩ := hfacts
  have hfirst : firstZ len up < 256 := hzi0 ▸ hzi 0 hN0
  unfold layer
  rw [ite_eq_right (by omega : ¬ len < 4)]
  refine WP.seq (WP.mono (preLayer_ok len up (by omega) s) fun s₁ ⟨⟨⟨hx2,hx3,hm1⟩,k1⟩,hv1⟩ => ?_)
  refine WP.seq (WP.mono (counter4_ok (128/len) (by omega) s₁)
    fun s₂ ⟨⟨⟨hcnt,hm2⟩,k2⟩,hv2⟩ => ?_)
  have c2 : VConsts s₂ := ⟨by rw [hv2,hv1]; exact hc.q, by rw [hv2,hv1]; exact hc.qi⟩
  refine WP.mono (wp_countdown (cnt := .x4) (N := 128/len) (by omega) hN0
    (fun c s' => PolyIs s'.mem fP (layF blk F len zi c) ∧
      s'.gpr .x2 = coeffAddr fP (2*len*c) ∧ s'.gpr .x3 = coeffAddr zP (zi c) ∧
      BInv fP s₂ s' ∧ Tab tab s'.mem zP 256)
    (fun c hcc s' ⟨hp,hx2',hx3',hi,ht'⟩ _ => ?_)
    ⟨by rw [hm2,hm1]; exact hP,
      by rw [k2.get .x2,hx2,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],
      by rw [k2.get .x3,hx3,h1,hzi0],BInv.refl c2,by rw [hm2,hm1]; exact ht⟩ hcnt)
    fun s' ⟨hp,_,_,hi,_⟩ => ⟨hp,⟨((k1.trans k2).trans hi.keep).mono,
      by simpa only [hm2,hm1] using hi.frame,hi.consts⟩⟩
  have hst : 2*len*c+2*len ≤ 256 := by
    have hh := Nat.mul_le_mul_left (2*len) (show c+1 ≤ 128/len by omega)
    rw [Nat.mul_succ,hcov] at hh; exact hh
  refine WP.mono (block_ok hbf hblk h4 hl hl4 hst (hzi c hcc) hzt up hx2' hx3' hi.consts hp ht'
    (by rw [hi.keep.wr,k2.wr,k1.wr]; exact hw)
    (by rw [hi.keep.rd,hi.keep.wr,k2.rd,k2.wr,k1.rd,k1.wr]; exact hzp))
    fun s'' ⟨hp',hx2'',hx3'',hc'',hi'⟩ =>
      ⟨⟨by rw [layF,foldl_range_succ]; exact hp',by rw [hx2'',Nat.mul_succ],
        by rw [hx3'',hx3',hstep c hcc],hi.trans hi',ht'.frame hi'.frame (by simpa using hd) (by decide)⟩,hc''⟩
end
end VG.Proof.MlDsa.AArch64.Arith.Neon
