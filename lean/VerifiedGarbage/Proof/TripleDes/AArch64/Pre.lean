import VerifiedGarbage.Proof.TripleDes.AArch64.Block
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (Spec.TripleDes.blockAt s.mem (s.gpr .x1))
  pub := PublicRegs [.x0, .x1, .x2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
      (s.gpr .x0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  have scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x2, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have scratchReads : ∀ i < 64, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .x2, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keyContains : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      (⟨s.gpr .x0, 384⟩ : Region).Contains (keyAddr (componentBase (s.gpr .x0) c) direction j) 8 := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.contains_base _ (by omega) (by omega)
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .x0) c) direction j, 8⟩ ⟨s.gpr .x0, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega)
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .x2, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .x2, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => scratchReads i (by omega)),
    (fun i hi => scratchWrites i (by omega)), ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  · intro c hc direction j hj
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .x0, 384⟩, by simp, keyContains c hc direction j hj⟩
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .x0) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm


end VG.Proof.TripleDes.AArch64
