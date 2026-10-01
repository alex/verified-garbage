import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .r4).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 t) (zero : s.gpr .r0 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (State.addr (s.gpr .r4)) t).Disjoint ⟨State.addr (s.gpr .r6), 128⟩) :
    WP isa (.loop (.block copyKey) .ne) s (fun s' =>
      s'.gpr .r0 = BitVec.ofNat 32 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t
  let I (i : Nat) (s' : State) := s'.gpr .r0 = BitVec.ofNat 32 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .r4 (by decide)
  have outPtr := frame₁.reg .r6 (by decide)
  have len₁ := (frame₁.reg .r5 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r4 + s₁.gpr .r0)) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁, addr_add (by omega)]
    exact readable i hi
  have write₁ : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable i (by omega)
  have byte₁ : s₁.mem (State.addr (s₁.gpr .r4 + s₁.gpr .r0)) = key.getD i 0 := by
    rw [keyPtr, index₁, addr_add (by omega), bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁, addr_add (by omega : (s.gpr .r6).toNat + i < 2 ^ 32)] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega) _ keep₂', ?_⟩
    · rw [index₂, index₁, counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, counter_add]
    exact congrArg some (counter_eq (i + 1) t (by omega) (by omega))

end VG.Proof.Rc2.Arm
