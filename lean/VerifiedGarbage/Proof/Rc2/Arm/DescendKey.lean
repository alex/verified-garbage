import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop

/-! # The descending effective-key reduction loop -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem descendLoop_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r1 = BitVec.ofNat 32 t8) (start : s.gpr .r0 = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa (.loop (.block descendKey) .ne) s (fun s' =>
      s'.gpr .r0 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .r0 = BitVec.ofNat 32 (128 - t8 - j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .r0 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .r6 (by decide)
  have len₁ := (frame₁.reg .r1 (by decide)).trans len
  have indexNew : s₁.gpr .r0 - 1 = BitVec.ofNat 32 (127 - t8 - j) := by
    rw [index₁, counter_sub _ (show 1 ≤ 128 - t8 - j by omega)]
    congr 1; omega
  have loAddr : State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1) + 1) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc, counter_add]
    exact addr_add (by omega)
  have hiAddr : State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1 + s₁.gpr .r1)) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1))) 1 := by
    rw [frame₁.wr, outPtr, indexNew, addr_add (by omega)]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1) + 1)) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1 + s₁.gpr .r1))) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (descendKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, indexNew, addr_add (by omega)] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .r0 - 1 = _
      rw [indexNew]
      congr 1; omega
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .r0 - 1) == 0#32) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega
    have eqZero := counter_eq (127 - t8 - j) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.Arm
