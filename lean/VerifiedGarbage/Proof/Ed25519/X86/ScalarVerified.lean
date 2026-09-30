import VerifiedGarbage.Proof.Ed25519.X86.ScalarMain
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) : VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  obtain ⟨hp, _, ho⟩ := scalarReduce_pre h
  exact scalarTaint_wf hp ho h.2.1 h.2.2.2.2.1

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := (scalarReduce_pre hs).1
  have pt := (scalarReduce_pre ht).1
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

def scalarSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def scalarSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := scalarSatMem
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct h

def scalarReduceWide : Contract isa :=
  { scalarReduceLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarReduceRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 64⟩, ⟨argAddr s 0, 12⟩]
def scalarReduceWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarReduceWide_pre (s : State) (h : scalarReduceWide.pre s) :
    scalarReduceLocal.pre (s.withRegions (scalarReduceRd s) (scalarReduceWr s)) := by
  simp only [scalarReduceLocal, scalarReduceRd, scalarReduceWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarReduceWide_implies : scalarReduceWide.Implies (Spec.Ed25519.scalarReduceContract X86.abi) := by
    have a0 : arg scalarSatState 0 = 0x1000 := by decide
    have a1 : arg scalarSatState 1 = 0x2000 := by decide
    have a2 : arg scalarSatState 2 = 0x4000 := by decide
    have e : argAddr scalarSatState 0 = 0x8004 := by decide
    have esp : scalarSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarReduceContract, Spec.Ed25519.scalarReduceSig,
      Spec.Ed25519.scratchWords, scalarReduceWide, scalarReduceLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using scalarSatState

theorem scalarReduce_verified : Verified X86.target scalarReduce (Spec.Ed25519.scalarReduceContract X86.abi) := by
  have hsat := scalarReduceWide_implies.sat_left
  have satLocal : ∃ s, scalarReduceLocal.pre s := hsat.elim fun s h => ⟨_, scalarReduceWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarReduce scalarReduceLocal :=
    Verified.of_correct scalarReduce_ok scalarReduce_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarReduceRd scalarReduceWr scalarReduceWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarReduceWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarReduceRd, scalarReduceWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarReduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarReduceWide, scalarReduceLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarReduceWide, scalarReduceLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86
