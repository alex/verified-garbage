import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Init
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# TDEA-CMAC on ARMv7: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/Arm/Taint.lean`) checks that only the arguments, which are
public, decide branches and addresses. The functions keep their pointers
and counts in words 28–30 of the scratch buffer, the second writable
region: the analysis knows `r10` points at it (copied from `r3` in `init`,
loaded from the stack argument in the others), so the words stored there
through `r10` are public, and stores through other pointers come before
the pointers are stored back.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm
open VG.Proof.MdStream.Arm (addr_toNat)

/-- `init`'s initial taint: the arguments are public; `r2` and `r3` point at
the output and the scratch buffer. -/
def initTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [400, 640], bases := [(.r2, 0), (.r3, 1)] }

/-- `update`'s and `finalize`'s: the arguments are public; `r1` points at
the state, and the stack argument at the scratch buffer. -/
def streamTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [8, 640], bases := [(.r1, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem initTaint_wf {s : State} (h : initArm.pre s) : VG.Arm.Taint.Wf initTaint s := by
  have hp := IPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, initTaint], ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_scr
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.out_fit; have := hp.scr_fit
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem streamTaint_wf {s : State} (hwr : s.wr = [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (stackArg s 0), 640⟩])
    (st_scr : Region.Disjoint ⟨State.addr (s.gpr .r1), 8⟩ ⟨State.addr (stackArg s 0), 640⟩)
    (st_args : Region.Disjoint ⟨State.addr (s.gpr .r1), 8⟩ ⟨stackArgAddr s 0, 4⟩)
    (scr_args : Region.Disjoint ⟨State.addr (stackArg s 0), 640⟩ ⟨stackArgAddr s 0, 4⟩)
    (st_fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32) (scr_fit : (stackArg s 0).toNat + 640 ≤ 2 ^ 32)
    (sp_fit : s.sp.toNat + 4 ≤ 2 ^ 32) : VG.Arm.Taint.Wf streamTaint s := by
  have e : (⟨State.addr s.sp, 4⟩ : Region) = ⟨stackArgAddr s 0, 4⟩ := by simp [stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hwr, streamTaint], ?_, ?_⟩, fun p hp' => ?_, fun _ => ⟨sp_fit, ?_⟩, ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact st_scr
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [streamTaint, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hwr]
  · simp only [streamTaint, e, hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact st_args.symm
    · exact scr_args.symm
  · intro p hp'
    simp only [streamTaint, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem argByte_eq (s : State) (k : Nat) : VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

/-- Two runs agree on `streamTaint` when they agree on the arguments. -/
theorem streamTaint_agree {s t : State} (hs : VG.Arm.Taint.Wf streamTaint s) (ht : VG.Arm.Taint.Wf streamTaint t)
    (hws : s.wr = [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (stackArg s 0), 640⟩])
    (hwt : t.wr = [⟨State.addr (t.gpr .r1), 8⟩, ⟨State.addr (stackArg t 0), 640⟩])
    (hsp : s.sp = t.sp) (h0 : s.gpr .r0 = t.gpr .r0) (h1 : s.gpr .r1 = t.gpr .r1) (h2 : s.gpr .r2 = t.gpr .r2)
    (h3 : s.gpr .r3 = t.gpr .r3) (ha : stackArg s 0 = stackArg t 0) : VG.Arm.Taint.Agree streamTaint s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp, fun k hk => ?_⟩
  · simp only [streamTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hws, hwt, h1, ha]
  · rw [argByte_eq, argByte_eq, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init := by
  refine VG.Taint.constantTime (A := taint) initTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, initTaint_wf hs, initTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [initTaint])⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [(IPre.of hs).wr, (IPre.of ht).wr, outR, outR, iscrR, iscrR, O, O, Sc, Sc, h2, h3]

theorem update_ct : ConstantTime isa updateArm.pre updateArm.pub update := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  have ps := UPre.of hs
  have pt := UPre.of ht
  exact streamTaint_agree
    (streamTaint_wf ps.wr ps.st_scr ps.st_args ps.scr_args ps.st_fit ps.scr_fit ps.sp_fit)
    (streamTaint_wf pt.wr pt.st_scr pt.st_args pt.scr_args pt.st_fit pt.scr_fit pt.sp_fit)
    ps.wr pt.wr hsp h0 h1 h2 h3 ha

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  have ps := FPre.of hs
  have pt := FPre.of ht
  exact streamTaint_agree
    (streamTaint_wf ps.wr ps.st_scr ps.st_args ps.scr_args ps.st_fit ps.scr_fit ps.sp_fit)
    (streamTaint_wf pt.wr pt.st_scr pt.st_args pt.scr_args pt.st_fit pt.scr_fit pt.sp_fit)
    ps.wr pt.wr hsp h0 h1 h2 h3 ha

end VG.Proof.CmacTripleDes.Arm
