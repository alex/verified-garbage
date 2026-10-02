import VerifiedGarbage.Proof.AesGcm.X86.Flush

/-!
# AES-GCM on x86: calling `vg_aes_ctr32` from the pieces

Untrusted: everything here is checked by Lean. The arguments of
`vg_aes_ctr32` in their registers (`CtrReady`): the key schedule at the
context, the rounds, a counter block `C`, `nb` blocks at `Dp` and the
working space `W + 512`; the call and `ebp` back to `W` (`ctrW_ok`,
`CtrOut`) and its constant time (`ctrW_ct`). The number of rounds is kept
at `W + roundsO` (`RoundsAt`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32)

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : BitVec 32) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m (w64 Ctx) (16 * (R + 1)))

/-- The number of rounds, kept at `W + roundsO`. -/
def RoundsAt (m : Mem) (W : BitVec 32) (R : Nat) : Prop :=
  slotv m W roundsO = BitVec.ofNat 32 R ∧ (R = 10 ∨ R = 12 ∨ R = 14)

/-- The kept values (and our caller's registers): `W + 128` to `W + 240`. -/
abbrev keptR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 128, 112⟩

theorem rounds_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32}
    (hd : ∀ r ∈ rs, (keptR W).Disjoint r) {R : Nat} (h : RoundsAt m W R) : RoundsAt m' W R :=
  ⟨by rw [slotv_eq, slot_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))];
      exact h.1, h.2⟩

theorem ctx_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32}
    (hd : ∀ r ∈ rs, (keptR W).Disjoint r) :
    m'.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = m.readW (w64 W + BitVec.ofNat 64 ctxO) 32 :=
  slot_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))

theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Ctx : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 Ctx, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' Ctx R = ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem covers_pre {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p, n⟩] rs := by
  have := covers_off (d := 0) (n := n) h (by omega) hk
  rwa [BitVec.add_zero] at this

/-- The call of `vg_aes_ctr32` and `ebp` back to `W`. -/
abbrev ctrW : Prog isa := .seq ctrCall (.block unscr)

/-- Ready for `ctrW`: the arguments of `vg_aes_ctr32` in their registers. -/
structure CtrReady (Ctx St W SP : BitVec 32) (R : Nat) (C Dp : BitVec 32) (nb : Nat) (s : State) : Prop where
  eax : s.gpr .eax = Ctx
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = Dp
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  ebp : s.gpr .ebp = W + BitVec.ofNat 32 512
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx
  rounds : RoundsAt s.mem W R
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * nb ≤ 2 ^ 32
  wC : Covers [⟨w64 C, 16⟩] s.wr
  wD : Covers [⟨w64 Dp, 16 * nb⟩] s.wr
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  kC : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kD : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 Dp, 16 * nb⟩
  sC : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 2048⟩
  sD : (⟨w64 Dp, 16 * nb⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 2048⟩
  bC : (below SP 28).Disjoint ⟨w64 C, 16⟩
  bD : (below SP 28).Disjoint ⟨w64 Dp, 16 * nb⟩
  pC : (keptR W).Disjoint ⟨w64 C, 16⟩
  pD : (keptR W).Disjoint ⟨w64 Dp, 16 * nb⟩

/-- What `ctrW` leaves. -/
structure CtrOut (Ctx St W SP : BitVec 32) (R : Nat) (C Dp : BitVec 32) (nb : Nat) (s s' : State) : Prop where
  env : Env Ctx St W SP s'
  rounds : RoundsAt s'.mem W R
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 Dp, 16 * nb⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28] s.mem s'.mem
  out : blocksAt s'.mem (w64 Dp) nb = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 Dp) nb)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 nb (blockAt s.mem (w64 C))
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) (hK : K = 28)
include L hK

theorem CtrReady.call {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP R C Dp nb s) :
    CtrCall s Ctx C Dp (W + BitVec.ofNat 32 512) R nb := by
  have eS := L.aW (o := 512) (by decide)
  have hsp : below (s.gpr .esp) 28 = below SP 28 := by rw [h.esp]
  refine ⟨h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp, h.rounds.2, by rw [h.esp]; have := L.sp; omega,
    h.kC.sub_left (Region.sub_prefix (by decide)), h.kD.sub_left (Region.sub_prefix (by decide)), ?_, h.cd,
    by rw [eS]; exact h.sC, by rw [eS]; exact h.sD, by rw [hsp]; subst hK; exact L.kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp]; exact h.bC, by rw [hsp]; exact h.bD, ?_, by have := L.fc; omega, h.fC, h.fD, ?_,
    covers_pre h.ctxR (by decide) (by decide), ?_⟩
  · rw [eS]; exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · rw [hsp, eS]; subst hK; exact L.kw.sub_right (Lay.wSub (by decide))
  · rw [L.nW (by decide)]; have := L.fw; omega
  · rw [eS]; exact covers_cons h.wC (covers_cons h.wD (covers_cons (covers_off h.wW (by decide) (by decide))
      covers_nil))

theorem CtrReady.kept {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP R C Dp nb s) :
    ∀ r ∈ [(⟨w64 C, 16⟩ : Region), ⟨w64 Dp, 16 * nb⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28],
      (keptR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.pC
  · exact h.pD
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · subst hK; exact (L.stk_w (by decide)).symm

theorem ctrW_ok {R : Nat} {C Dp : BitVec 32} {nb : Nat} {s : State}
    (h : CtrReady Ctx St W SP R C Dp nb s) :
    WP isa ctrW s (CtrOut Ctx St W SP R C Dp nb s) := by
  have eS := L.aW (o := 512) (by decide)
  refine WP.seq (WP.mono (ctr_call (h.call L hK)) fun s₁ g => ?_)
  have gf := g.frame
  have hsp : below (s.gpr .esp) 28 = below SP 28 := by rw [h.esp]
  rw [eS, hsp] at gf
  have hk := h.kept L hK
  have bp₁ : s₁.gpr .ebp = W + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.ebp]
  refine WP.of_runBlock ⟨_, by xrun [unscr, bp₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, gf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, bp₁]; exact BitVec.add_sub_cancel _ _
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esi (by decide), h.esi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .esp (by decide), h.esp]
  · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, g.rd, g.wr]; exact h.ctxR
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.stW
  · simp only [wr_setReg, wr_arithFlags, g.wr]; exact h.wW
  · simp only [mem_setReg, mem_arithFlags]; rw [ctx_frame gf hk, h.ctx]
  · simp only [mem_setReg, mem_arithFlags]; exact rounds_frame gf hk h.rounds
  · simp only [mem_setReg, mem_arithFlags]; exact g.out
  · simp only [mem_setReg, mem_arithFlags]; exact g.ctr
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .ebx (by decide)]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, g.saved .edi (by decide)]
  · mems [g.rd]
  · mems [g.wr]

theorem ctrW_ct {R : Nat} {C Dp : BitVec 32} {nb : Nat} : CT (CtrReady Ctx St W SP R C Dp nb) ctrW := by
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 512)
    (ctr_ct (E := SP) fun s h => ⟨h.call L hK, h.esp⟩) (fun s h => WP.mono (ctr_call (h.call L hK))
      fun s₁ g => by rw [g.saved .ebp (by decide), h.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

end

end VG.Proof.AesGcm.X86
