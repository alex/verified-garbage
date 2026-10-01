import VerifiedGarbage.Proof.Ed25519.X86.MulAddMain
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  obtain ⟨hp, _, _, _, ho⟩ := scalarMulAdd_pre h
  obtain ⟨_, wr, _, _, _, _, ao, _⟩ := h
  exact scalarTaint_wf hp ho wr ao

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := (scalarMulAdd_pre hs).1
  have pt := (scalarMulAdd_pre ht).1
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

def mulAddSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x38 else if a = 0x8015 then 0x40 else 0

def mulAddSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := mulAddSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x3800, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct h

def scalarMulAddWide : Contract isa :=
  { scalarMulAddLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def scalarMulAddRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 32⟩, ⟨argAddr s 0, 20⟩]
def scalarMulAddWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem scalarMulAddWide_pre (s : State) (h : scalarMulAddWide.pre s) :
    scalarMulAddLocal.pre (s.withRegions (scalarMulAddRd s) (scalarMulAddWr s)) := by
  simp only [scalarMulAddLocal, scalarMulAddRd, scalarMulAddWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarMulAddWide_implies : scalarMulAddWide.Implies (Spec.Ed25519.scalarMulAddContract X86.abi) := by
    have a0 : arg mulAddSatState 0 = 0x1000 := by decide
    have a1 : arg mulAddSatState 1 = 0x2000 := by decide
    have a2 : arg mulAddSatState 2 = 0x3000 := by decide
    have a3 : arg mulAddSatState 3 = 0x3800 := by decide
    have a4 : arg mulAddSatState 4 = 0x4000 := by decide
    have e : argAddr mulAddSatState 0 = 0x8004 := by decide
    have esp : mulAddSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, scalarMulAddWide, scalarMulAddLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, e, esp] using mulAddSatState

theorem scalarMulAdd_verified : Verified X86.target scalarMulAdd (Spec.Ed25519.scalarMulAddContract X86.abi) := by
  have hsat := scalarMulAddWide_implies.sat_left
  have satLocal : ∃ s, scalarMulAddLocal.pre s := hsat.elim fun s h => ⟨_, scalarMulAddWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarMulAdd scalarMulAddLocal :=
    Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarMulAddRd scalarMulAddWr scalarMulAddWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarMulAddWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarMulAddRd, scalarMulAddWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarMulAddWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86
