import VerifiedGarbage.Proof.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 384⟩
    let data : Region := ⟨s.gpr .rsi, 8⟩
    let scratch : Region := ⟨s.gpr .rdx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .rsi) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))
  pub := PublicRegs [.rdi, .rsi, .rdx]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)))
      (s.gpr .rdi) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, _, _⟩ := hs
  have scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have scratchReads : ∀ i < 64, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .rdx, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keyContains : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      (⟨s.gpr .rdi, 384⟩ : Region).Contains (keyAddr (componentBase (s.gpr .rdi) c) direction j) 8 := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.contains_base _ (by omega) (by omega)
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .rdi) c) direction j, 8⟩ ⟨s.gpr .rdi, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega)
  have workSub : Region.Sub (workRegion s) ⟨s.gpr .rdx, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .rdx, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => scratchReads i (by omega)),
    (fun i hi => scratchWrites i (by omega)), scratchReads 7 (by decide),
    scratchWrites 7 (by decide), ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  · intro c hc direction j hj
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .rdi, 384⟩, by simp, keyContains c hc direction j hj⟩
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .rdi) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm


theorem blockTaint_wf (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    Taint.Wf blockTaint s := by
  obtain ⟨_, hwr, _, dataSep, _, _⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 8; decide)
        (List.Forall₂.cons (by change 512 ≤ 512; decide) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 8 ≤ 2 ^ 64; decide
      · change 512 ≤ 2 ^ 64; decide
  · intro p hp
    simp only [blockTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rdx = s.gpr .rdx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem blockTaint_agree (d : Direction) (s t : State)
    (hs : (blockContract d).pre s) (ht : (blockContract d).pre t)
    (hp : (blockContract d).pub s t) : X86_64.Taint.Agree blockTaint s t := by
  refine ⟨?_, ?_, blockTaint_wf d s hs, blockTaint_wf d t ht, ?_, ?_, ?_⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [blockTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [blockTaint, RegSet.not_mem_empty] at hr

end VG.Proof.TripleDes.X86_64
