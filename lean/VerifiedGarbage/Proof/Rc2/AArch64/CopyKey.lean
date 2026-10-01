import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa (.loop (.block copyKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (s.gpr .x19) t
  let I (i : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .x19 (by decide)
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x19 + s₁.gpr .x23) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁]
    exact readable i hi
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable i (by omega)
  have byte₁ : s₁.mem (s₁.gpr .x19 + s₁.gpr .x23) = key.getD i 0 := by
    rw [keyPtr, index₁, bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁] using keep₂
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

end VG.Proof.Rc2.AArch64
