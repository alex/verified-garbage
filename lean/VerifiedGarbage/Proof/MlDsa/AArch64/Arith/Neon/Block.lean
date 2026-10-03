import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Table

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown imm16)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq PolyIs)

abbrev clob : List Reg := [.x2,.x3,.x4,.x5,.x6]

structure BInv (fP : Addr) (s s' : State) : Prop where
  keep : Keep clob s s'
  frame : Frame [pR fP] s.mem s'.mem
  consts : VConsts s'

theorem BInv.refl {p : Addr} {s : State} (hc : VConsts s) : BInv p s s :=
  ⟨Keep.refl _ _, Frame.refl _ _,hc⟩

theorem BInv.trans {p : Addr} {s₁ s₂ s₃ : State} (h₁ : BInv p s₁ s₂) (h₂ : BInv p s₂ s₃) :
    BInv p s₁ s₃ := ⟨(h₁.keep.trans h₂.keep).mono,h₁.frame.trans h₂.frame,h₂.consts⟩

theorem counter5_ok (N : Nat) (hN : N < 65536) (s : State) :
    WP isa (.block [.movz .x .x5 (BitVec.ofNat 16 N) 0]) s fun s' =>
      ((s'.gpr .x5 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hN]

theorem blockEnd_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 (4*len),.subImm .x .x4 .x4 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+BitVec.ofNat 64 (4*len) ∧ s'.gpr .x4 = s.gpr .x4-1 ∧
        s'.mem = s.mem) ∧ Keep [.x2,.x4] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [show 4*len < 4096 by omega]
  rfl

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem block_ok {fP zP : Addr} {len st k : Nat} (h4 : 4 ≤ len) (hl : len ≤ 128)
    (hl4 : len%4 = 0) (hs : st+2*len ≤ 256) (hk : k < 256)
    {tab : Nat → Nat} (hzt : TabZ tab zt) (up : Bool) {G : Poly} {s : State}
    (hx : s.gpr .x2 = coeffAddr fP st) (h3 : s.gpr .x3 = coeffAddr zP k)
    (hc : VConsts s) (hP : PolyIs s.mem fP G) (ht : Tab tab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (block bf len up) s fun s' =>
      PolyIs s'.mem fP (blk G len k st len) ∧ s'.gpr .x2 = coeffAddr fP (st+2*len) ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧
      s'.gpr .x4 = s.gpr .x4-1 ∧ BInv fP s s' := by
  have hN : len/4 < 65536 := by omega
  have hN0 : 0 < len/4 := by omega
  have hcov : 4*(len/4) = len := by omega
  unfold block
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (zetas_large_ok hzt (by omega) (by omega) up hk h3 ht hzp hc)
    fun s₁ ⟨lz,c₁,h31,hm₁,k₁⟩ => ?_
  refine WP.mono (counter5_ok (len/4) hN s₁) fun s₂ ⟨⟨⟨hcnt,hm₂⟩,k₂⟩,hv₂⟩ => ?_
  have c₂ : VConsts s₂ := ⟨by rw [hv₂]; exact c₁.q, by rw [hv₂]; exact c₁.qi⟩
  have z₂ : Zetas (s₂.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) := by rw [hv₂]; exact lz
  refine WP.seq (WP.mono (wp_countdown (cnt := .x5) (N := len/4) (by omega) hN0
    (fun u s' => PolyIs s'.mem fP (blk G len k st (4*u)) ∧
      s'.gpr .x2 = coeffAddr fP (st+4*u) ∧ s'.v .v18 = s₂.v .v18 ∧ Keep [.x2,.x5] s₂ s' ∧ BInv fP s₂ s')
    (fun u hu s' ⟨hp,hx',hv',hki,hi⟩ _ => ?_)
    ⟨by rw [hblk.zero,hm₂,hm₁]; exact hP,
      by rw [k₂.get .x2,k₁.get .x2,hx]; rfl,rfl,Keep.refl _ _,BInv.refl c₂⟩ hcnt)
    fun s₃ ⟨hp,hx3,hv3,hki3,hi3⟩ => ?_)
  · refine WP.mono (step_ok hbf hblk (by omega) hl4 hs (by omega) hi.consts
      (by rw [hv']; exact z₂) hx' hp (by rw [hi.keep.wr,k₂.wr,k₁.wr]; exact hw))
      fun s'' ⟨hp',hf',hc',hv'',hx'',hcnt',hk'⟩ =>
        ⟨⟨hp',hx'',hv''.trans hv',(hki.trans hk').mono,hi.trans ⟨hk'.mono,hf',hc'⟩⟩,hcnt'⟩
  · refine WP.mono (blockEnd_ok len hl s₃) fun s₄ ⟨⟨⟨hx4,hcnt4,hm4⟩,k₄⟩,hv4⟩ =>
      ⟨by rw [hm4]; simpa only [hcov] using hp, ?_, ?_, ?_,
        ⟨(((k₁.trans k₂).trans hi3.keep).trans k₄).mono, ?_,
          ⟨by rw [hv4]; exact hi3.consts.q, by rw [hv4]; exact hi3.consts.qi⟩⟩⟩
    · rw [hx4,hx3,hcov,coeffAddr_add,show st+len+len = st+2*len by omega]
    · rw [k₄.get .x3,hki3.get .x3,k₂.get .x3,h31]
    · rw [hcnt4,hki3.get .x4,k₂.get .x4,k₁.get .x4]
    · rw [hm4]; simpa only [hm₂,hm₁] using hi3.frame
end
end VG.Proof.MlDsa.AArch64.Arith.Neon
