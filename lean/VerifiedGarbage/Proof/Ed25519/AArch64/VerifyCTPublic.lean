import VerifiedGarbage.Proof.Ed25519.AArch64.WindowCT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext

/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) (kt : VerifyKeep base s t) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs t :=
  ⟨h.context.of_keep kt, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552]) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  all_goals
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1 h.2

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    CT (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r t) verifyEquationPoints (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r x) :
      WP isa windowPrep x (SkipRun R₀ base challenge sig Aa K S 32) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarBytes
      c.scalarFar c.challengeRead c.challengeFar (by rw [h.2.1]; exact hA)) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we, Nat.div_eq_of_lt (show Spec.Ed25519.decodeLE kbs < 256 ^ (32 + 32) from we.kVal ▸ decodeLE_lt64 _ _), by decide,
      by decide⟩
  have wn (x : State) (h : LoopRun R₀ base challenge sig Aa K S 0 x) :
      WP isa (.block negR) x (EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [pow_zero, Nat.div_one] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨ku.scr hx.ctx.scratch, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg.proj
  have prepCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) windowPrep (fun _ _ => True) := by
    rw [windowPrep]
    exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  have negRCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block negR) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  refine CT.seq ((CT.wp (x0_ct (fun x h => h.1.context.scratch.x0) prepCT)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.seq skipZero_ct ?_
  refine CT.seq (fun x y tx ty x' y' ⟨hsp, c, hc32, hc64, hx, hy⟩ ex ey =>
    windowsA_ct hc32 hc64 x y tx ty x' y' ⟨hsp, hx, hy⟩ ex ey) ?_
  refine CT.seq loopB_ct ?_
  exact seq_same (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0) negRCT) wn
    (pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.AArch64
