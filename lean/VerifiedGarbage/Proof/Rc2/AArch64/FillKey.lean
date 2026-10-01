import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop

/-! # Forward expansion to 128 bytes -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem fillLoop_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 key.length) (start : s.gpr .x23 = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 (key.length + j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .x23 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have loAddr : s₁.gpr .x21 + s₁.gpr .x23 - 1#64 =
      s.gpr .x21 + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁]
    exact Offset.add_ofNat_sub _ (by omega)
  have hiAddr : s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20) =
      s.gpr .x21 + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega), Nat.add_sub_cancel_left]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + s₁.gpr .x23 - 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (fillKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, index₁] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1, index₁, counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega
    change some ((BitVec.ofNat 64 (key.length + j + 1) - BitVec.ofNat 64 128) == 0#64) = _
    rw [counter_eq _ _ (by omega) (by decide)]
    simp only [he]

end VG.Proof.Rc2.AArch64
