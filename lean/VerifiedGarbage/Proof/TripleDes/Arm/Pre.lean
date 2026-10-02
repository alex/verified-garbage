import VerifiedGarbage.Proof.TripleDes.Arm.Block
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Arm.ConstantTime
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 512 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))
  pub := PublicRegs [.r0, .r1, .r2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (keyAddr (componentBase base c) d j) t =
      State.addr base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j) + 4 * t) := by
  have bound := selectedRound_bound d j hj
  rw [wordAddr, keyAddr_component, Offset.add_ofNat_add_ofNat,
    addr_add (by omega_using [fit, hc, bound, ht])]

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    readKey m (keyAddr (componentBase base c) d j) =
      m.readW (State.addr base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j))) 64 := by
  rw [readKey, keyWordAddress base fit c j 1 hc hj (by decide) d,
    keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact readW_pair m _

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))))
      (s.gpr .r0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, keyFit, dataFit, scratchFit⟩ := hs
  have scratchWrites : ∀ i < 128, InRegions s.wr (wordAddr (s.gpr .r2) i) 4 := by
    intro i hi
    rw [wordAddr, addr_add (by omega_using [scratchFit, hi]), hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have scratchSaveWrites : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have scratchSaveReads : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := scratchSaveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, scratchFit, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (keyAddr (componentBase (s.gpr .r0) c) direction j) t, 4⟩
        ⟨State.addr (s.gpr .r0), 384⟩ := by
    intro c hc direction j hj t ht
    rw [keyWordAddress _ keyFit c j t hc hj ht direction]
    have bound := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, bound, ht])
  have workSub : Region.Sub (spillRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Region.sub_prefix (by decide)
  refine ⟨spills, by omega_using [scratchFit], dataFit, rfl, scratchSaveReads,
    scratchSaveWrites, ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [addr_add (by omega_using [dataFit, ht]), hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  · intro c hc direction j hj t ht
    rw [keyWordAddress _ keyFit c j t hc hj ht direction, hrd, hwr]
    have bound := selectedRound_bound direction j hj
    exact ⟨⟨State.addr (s.gpr .r0), 384⟩, by simp,
      Offset.contains_base _ (by omega_using [hc, bound, ht]) (by omega_using [hc, bound, ht])⟩
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right workSub
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right saveSub
  · intro c hc direction j hj
    rw [readKey_component s.mem _ keyFit c j hc hj direction]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (State.addr (s.gpr .r0)) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

end VG.Proof.TripleDes.Arm
