import VerifiedGarbage.Proof.TripleDes.X86.Ready
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.Schedule

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight
open VG.Spec.TripleDes (Direction)
open VG.Proof.Rc2.X86 (addr32)
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
      addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j) + 4 * t) := by
  have bound := selectedRound_bound d j hj
  rw [wordAddr, keyAddr_component]
  unfold addr
  rw [Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.addr_add (by omega)

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    readKey m (keyAddr (componentBase base c) d j) =
      m.readW (addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j))) 64 := by
  rw [readKey, keyWordAddress base fit c j 1 hc hj (by decide) d,
    keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact readW_pair m _

theorem ready_of_regions (s : State) (base : BitVec 32) (hok : Ok sboxCfg s)
    (hb : scheduleArg s = base) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (hread : ∀ p, (⟨addr32 base, 384⟩ : Region).Contains p 4 → InRegions (s.rd ++ s.wr) p 4)
    (hdis : (⟨addr32 base, 384⟩ : Region).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (workRegion s)) :
    Ready (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 base))) base s := by
  have workSub : Region.Sub (workRegion s) ⟨addr32 (s.gpr .ebp), 512⟩ :=
    Offset.sub_base _ (by decide)
  have keySub : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ ⟨addr32 base, 384⟩ := by
    intro c hc d j hj t ht
    rw [keyWordAddress base fit c j t hc hj ht d]
    have bound := selectedRound_bound d j hj
    exact Offset.sub_base _ (by omega)
  refine ⟨hok, hb, harg, hargSep, ?_, ?_, ?_, ?_⟩
  · intro c hc d j hj t ht
    apply hread
    rw [keyWordAddress base fit c j t hc hj ht d]
    have bound := selectedRound_bound d j hj
    exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj t ht
    exact (hdis.sub_left (keySub c hc d j hj t ht)).sub_right workSub
  · intro c hc d j hj k hk t ht
    have scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32 := hok.fit
    apply hdis.symm.sep
    · rw [wordAddr, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [keyWordAddress base fit c j t hc hj ht d]
      have bound := selectedRound_bound d j hj
      exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj
    rw [readKey_component s.mem base fit c j hc hj d]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (addr32 base) c
      (selectedRound d j) hc (selectedRound_bound d j hj)).symm

end VG.Proof.TripleDes.X86
