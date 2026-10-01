import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMain
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! The complete 512-bit scalar reducer meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct (ScalarReducePre.of hs)

def scalarTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [32, 8192], bases := [(.r2, 1)] }

theorem scalarTaint_wf {s : State} (h : scalarReduceLocal.pre s) : VG.Arm.Taint.Wf scalarTaint s := by
  have hp := ScalarReducePre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarTaint], ?_, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f2
  · intro p hm
    simp only [scalarTaint, List.mem_singleton] at hm
    subst hm
    simp [VG.Arm.Taint.region, hp.wr]

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) scalarTaint ?_ (by taint_decide)
  intro s t hs ht ⟨_, h0, h1, h2⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarTaint_wf hs, scalarTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [(ScalarReducePre.of hs).wr, (ScalarReducePre.of ht).wr, h0, h2]

theorem scalarReduce_verified : Verified Arm.target scalarReduce
    (Spec.Ed25519.scalarReduceContract Arm.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Spec.Ed25519.scalarReduceContract, Spec.Ed25519.scalarReduceSig,
      Spec.Ed25519.scratchWords, scalarReduceLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarSatState)

end VG.Proof.Ed25519.Arm
