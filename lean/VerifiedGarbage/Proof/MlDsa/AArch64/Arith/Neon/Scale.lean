import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (movW_ok wp_countdown)
open VG.Proof.MlKem.AArch64 (Keep Lanes wp_ldrq wp_strq wp_vop wp_scalar)
open VG.Spec.MlDsa (q Poly Zq PolyIs coeffAt)

def Scaled (G : Poly) (m : Mem) (p : Addr) (u : Nat) : Prop :=
  ∀ j < 256, (coeffAt m p j).toNat = if j < 4*u then (G[j]!*8347681).val else (G[j]!).val

/-- Four coefficients multiplied by 256⁻¹, with canonical outputs. -/
theorem scaleStep_ok {p : Addr} {G : Poly} {u : Nat} (hu : u < 64) {s : State}
    (hc : VConsts s) (hz : Lanes (s.v .v18) (fun _ => 16382))
    (hx : s.gpr .x2 = coeffAddr p (4*u)) (hp : Scaled G s.mem p u) (hw : pR p ∈ s.wr) :
    WP isa (.block scaleBody) s fun s' => Scaled G s'.mem p (u+1) ∧
      s'.gpr .x2 = coeffAddr p (4*(u+1)) ∧ s'.gpr .x5 = s.gpr .x5-1 ∧
      Frame [pR p] s.mem s'.mem ∧ VConsts s' ∧ s'.v .v18 = s.v .v18 ∧ Keep [.x2,.x5] s s' := by
  have hj : 4*u+4 ≤ 256 := by omega
  unfold scaleBody
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (by decide) (by rw [hx,BitVec.add_zero])
    ⟨_,List.mem_append_right _ hw,vector_contains _ hj⟩ fun s₁ h1 => ?_
  have a1 : Lanes (s₁.v .v0) (fun e => (G[4*u+e]!).val) := by
    intro e he
    rw [h1.v,vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,hp _ (by omega),ite_eq_right (by omega)]
  have z1 : Lanes (s₁.v .v18) (fun _ => 16382) := by rw [h1.get .v18]; exact hz
  have hm : ∀ e < 4, VG.Proof.MlDsa.Arith.mont ((G[4*u+e]!).val*16382) < 2*q := by
    intro e he
    have ha : (G[4*u+e]!).val < 2^32 := Nat.lt_trans (G[4*u+e]!).isLt (by decide)
    have hzlt : 16382 < q := by decide
    have hb := Nat.mul_lt_mul'' hzlt ha
    exact mont_lt (by simpa only [Nat.mul_comm] using hb)
  refine mont_lanes (by decide) (by decide) (hc.chg h1.chg) a1 z1 (fun _ _ => by decide)
    fun s₂ h2 l2 => ?_
  refine csub_ok (by decide) ((hc.chg h1.chg).chg h2).lanes_q l2 hm fun s₃ h3 l3 => ?_
  have v3 : Coeffs (s₃.v .v0) (fun e => G[4*u+e]!*8347681) := l3.congr fun e _ => by
    dsimp only
    rw [show 16382 = (8347681 : Zq).val*2^32%q by decide,mont_mulR,val_mul]
  have g3 : s₃.gpr = s.gpr := h3.gpr.trans (h2.gpr.trans h1.gpr)
  have m3 : s₃.mem = s.mem := h3.mem.trans (h2.mem.trans h1.mem)
  have k3 : Keep [] s s₃ := ((h1.keep.trans h2.keep).trans h3.keep).mono
  refine wp_strq (by decide) (by rw [g3,hx,BitVec.add_zero])
    (by rw [k3.wr]; exact ⟨_,hw,vector_contains _ hj⟩) fun s₄ h4 => ?_
  refine WP.mono (bodyEnd_ok s₄) fun s₅ ⟨⟨⟨hx5,hcnt5,hm5⟩,k5⟩,hv5⟩ =>
    ⟨?_,?_,by rw [hcnt5,h4.gpr,g3],?_,
      ⟨by rw [hv5,h4.v]; exact (((hc.chg h1.chg).chg h2).chg h3).q,
        by rw [hv5,h4.v]; exact (((hc.chg h1.chg).chg h2).chg h3).qi⟩,
      by rw [hv5,h4.v,h3.get .v18,h2.get .v18,h1.get .v18],((k3.trans h4.keep).trans k5).mono⟩
  · intro j hj'
    rw [hm5,h4.mem,m3,coeffAt_write16 _ _ hj _ hj']
    by_cases h : 4*u ≤ j ∧ j < 4*u+4
    · rw [ite_eq_left h,ite_eq_left (by omega),v3 _ (by omega)]
      dsimp only
      rw [show 4*u+(j-4*u) = j by omega]
    · rw [ite_eq_right h,hp j hj']
      by_cases h' : j < 4*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
  · rw [hx5,h4.gpr,g3,hx,show (16 : BitVec 64) = BitVec.ofNat 64 (4*4) from rfl,
      coeffAddr_add,show 4*u+4 = 4*(u+1) by omega]
  · rw [hm5,h4.mem,m3]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (vector_contains p hj)

/-- Initialize the inverse scaling factor, pointer and loop counter. -/
theorem scalePro_ok (s : State) (hc : VConsts s) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x6 16382 ++
      ([.vop (.dup .s4 .v18 .x6),Impl.MlKem.AArch64.mov .x2 .x0,.movz .x .x5 64 0] : List Instr))) s fun s' =>
      Lanes (s'.v .v18) (fun _ => 16382) ∧ s'.gpr .x2 = s.gpr .x0 ∧
      s'.gpr .x5 = 64 ∧ s'.mem = s.mem ∧ Keep [.x2,.x5,.x6] s s' ∧ VConsts s' := by
  refine wp_scalar (by rfl) (movW_ok .x6 16382 s) fun s₁ ⟨⟨h6,hm1⟩,k1⟩ hv1 => ?_
  refine wp_vop (d := .v18) rfl fun s₂ h2 => ?_
  have hscalar : WP isa (.block [Impl.MlKem.AArch64.mov .x2 .x0,.movz .x .x5 64 0]) s₂
      (fun s' => (s'.gpr .x2 = s₂.gpr .x0 ∧ s'.gpr .x5 = 64 ∧ s'.mem = s₂.mem) ∧ Keep [.x2,.x5] s₂ s') := by
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    arun [Impl.MlKem.AArch64.mov]
  refine WP.mono (VG.Proof.MlKem.AArch64.WP.keepV (by rfl) hscalar)
    fun s₃ ⟨⟨⟨hx3,hcnt3,hm3⟩,k3⟩,hv3⟩ =>
      ⟨?_,by rw [hx3,h2.gpr,k1.get .x0],hcnt3,by rw [hm3,h2.mem,hm1],
        ((k1.trans h2.keep).trans k3).mono,
        ⟨by rw [hv3,h2.get .v16,hv1]; exact hc.q,by rw [hv3,h2.get .v17,hv1]; exact hc.qi⟩⟩
  rw [hv3,h2.v,h6]
  exact VG.Proof.MlKem.AArch64.lanes_dup.congr fun _ _ => by decide

/-- Scale all 256 coefficients by the modular inverse of 256. -/
theorem scale_ok {p : Addr} {G : Poly} {s : State} (h0 : s.gpr .x0 = p)
    (hc : VConsts s) (hp : PolyIs s.mem p G) (hw : pR p ∈ s.wr) :
    WP isa scale s fun s' => PolyIs s'.mem p (G.map (· * 8347681)) := by
  refine WP.seq (WP.mono (scalePro_ok s hc) fun s₁ ⟨hz,hx,hcnt,hm,k1,c1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x5) (N := 64) (by decide) (by decide)
    (fun u s' => Scaled G s'.mem p u ∧ s'.gpr .x2 = coeffAddr p (4*u) ∧
      s'.v .v18 = s₁.v .v18 ∧ VConsts s' ∧ Keep [.x2,.x5] s₁ s')
    (fun u hu s' ⟨hp',hx',hz',hc',hk'⟩ _ => ?_)
    ⟨by intro j hj; rw [hm,ite_eq_right (by omega)]; exact polyIs_toNat hp hj,
      by rw [hx,h0]; simp only [coeffAddr,Nat.mul_zero,BitVec.add_zero],rfl,c1,Keep.refl _ _⟩ hcnt)
    fun s' ⟨hp',_,_,_,_⟩ => ?_
  · refine WP.mono (scaleStep_ok hu hc' (by rw [hz']; exact hz) hx' hp'
      (by rw [hk'.wr,k1.wr]; exact hw)) fun s'' ⟨hp'',hx'',hcnt'',_,hc'',hz'',hk''⟩ =>
      ⟨⟨hp'',hx'',hz''.trans hz',hc'',(hk'.trans hk'').mono⟩,hcnt''⟩
  · refine polyIs_of_toNat fun j hj => ?_
    rw [hp' j hj,ite_eq_left (by rw [n_eq] at hj; omega),map_mul_get _ _ hj]
end VG.Proof.MlDsa.AArch64.Arith.Neon
