import VerifiedGarbage.Proof.Rc2.X86.KeyLoop

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .ebp).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t) (zero : s.gpr .ecx = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (addr32 (s.gpr .ebp)) t).Disjoint ⟨addr32 (s.gpr .edi), 128⟩) :
    WP isa (.loop (.block copyKey) .ne) s (fun s' =>
      s'.gpr .ecx = BitVec.ofNat 32 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill (Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t
  let I (i : Nat) (s' : State) := s'.gpr .ecx = BitVec.ofNat 32 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .ebp (by decide)
  have outPtr := frame₁.reg .edi (by decide)
  have len₁ := (frame₁.reg .esi (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp + s₁.gpr .ecx)) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁, addr_add (by omega)]
    exact readable i hi
  have write₁ : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable i (by omega)
  have byte₁ : s₁.mem (addr32 (s₁.gpr .ebp + s₁.gpr .ecx)) = key.getD i 0 := by
    rw [keyPtr, index₁, addr_add (by omega), bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁, addr_add (by omega : (s.gpr .edi).toNat + i < 2 ^ 32)] using keep₂
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

end VG.Proof.Rc2.X86
