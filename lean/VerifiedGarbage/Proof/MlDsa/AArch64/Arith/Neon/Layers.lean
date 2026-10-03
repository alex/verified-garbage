import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Spec.MlDsa (Poly PolyIs)

private theorem lens_cases {len : Nat} (hl : len ∈ nttLens) :
    len = 128 ∨ len = 64 ∨ len = 32 ∨ len = 16 ∨ len = 8 ∨ len = 4 ∨ len = 2 ∨ len = 1 := by
  simpa only [nttLens,List.mem_cons,List.not_mem_nil,or_false] using hl

set_option linter.unusedSimpArgs false

theorem layer_fwd_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ nttLens)
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab zetaTab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bfly len true) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  have hl := lens_cases hlen
  by_cases hsmall : len < 4
  · have hp : len = 1 ∨ len = 2 := by omega
    exact layer_packed_ok bfly_spec nttBlk_ok hp zetaTab_eq true
      (fun c => 128/len+c) (fun u => 128/len+(4/len)*u)
      (by simp [firstZ])
      (by intro u hu e he; simp only [ite_true]; omega)
      (by intro u hu h; contradiction)
      (by intro u hu; rcases hp with rfl | rfl <;> simp only [baseZ,ite_true,Nat.reduceDiv] <;> omega)
      (by intro u hu; simp only [ite_true,Nat.mul_add,Nat.mul_one]; omega) h0 h1 hc hP ht hw hzp hd
  · have hl' : len ∈ [4,8,16,32,64,128] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    exact layer_large_ok bfly_spec nttBlk_ok hl' zetaTab_eq true (fun c => 128/len+c)
      (by simp [firstZ])
      (by intro c hc; rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Nat.reduceDiv] at * <;> omega)
      (by intro c hc; simp only [ite_true]; exact VG.Proof.MlDsa.AArch64.Arith.coeffAddr_next _ _)
      h0 h1 hc hP ht hw hzp hd

theorem layer_inv_ok {fP zP : Addr} {len : Nat} (hlen : len ∈ nttLens)
    {F : Poly} {s : State} (h0 : s.gpr .x0 = fP) (h1 : s.gpr .x1 = zP)
    (hc : VConsts s) (hP : PolyIs s.mem fP F) (ht : Tab negZetaTab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) (hd : (pR zP).Disjoint (pR fP)) :
    WP isa (layer bflyInv len false) s fun s' => PolyIs s'.mem fP (nttInvLayer F len) ∧ BInv fP s s' := by
  have hl := lens_cases hlen
  by_cases hsmall : len < 4
  · have hp : len = 1 ∨ len = 2 := by omega
    exact layer_packed_ok bflyInv_spec nttInvBlk_ok hp negZetaTab_eq false
      (fun c => 256/len-1-c) (fun u => 256/len-1-(4/len)*u)
      (by simp [firstZ])
      (by intro u hu e he; simp only [Bool.false_eq_true,ite_false]; omega)
      (by intro u hu _; rcases hp with rfl | rfl <;> simp only [Nat.reduceDiv] <;> omega)
      (by intro u hu; rcases hp with rfl | rfl <;> simp only [baseZ,Bool.false_eq_true,ite_false,Nat.reduceDiv] <;> omega)
      (by intro u hu; simp only [Bool.false_eq_true,ite_false,Nat.mul_add,Nat.mul_one]; omega) h0 h1 hc hP ht hw hzp hd
  · have hl' : len ∈ [4,8,16,32,64,128] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    exact layer_large_ok bflyInv_spec nttInvBlk_ok hl' negZetaTab_eq false (fun c => 256/len-1-c)
      (by simp [firstZ])
      (by intro c hc; rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Nat.reduceDiv] at * <;> omega)
      (by intro c hc; simp only [Bool.false_eq_true,ite_false]
          have hk : 1 ≤ 256/len-1-c := by
            rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [Nat.reduceDiv] at * <;> omega
          rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ hk]
          exact congrArg (coeffAddr zP) (by omega))
      h0 h1 hc hP ht hw hzp hd

end VG.Proof.MlDsa.AArch64.Arith.Neon
