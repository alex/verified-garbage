import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLane

/-! # Matrix invariant: completed lanes contain their RFC initialization blocks -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def Initialized (m : Mem) (base : Addr) (lanes q done : Nat) (h0 : List Byte) : Prop :=
  ∀ lane < lanes, ∀ column < q,
    blockAt m (base + BitVec.ofNat 64 (1024 * (lane * q + column))) =
      if lane < done ∧ column < 2 then parseBlock (Proof.Argon2.initialBytes h0 lane column)
      else zeroBlock

theorem cell_bound (lanes q lane column : Nat) (hl : lane < lanes) (hc : column < q) :
    lane * q + column < lanes * q := by
  have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at mul
  omega

theorem cell_sep (q j lane column : Nat) (hq : 2 ≤ q) (hc : column < q)
    (other : lane ≠ j ∨ 2 ≤ column) :
    1024 * (lane * q + column) + 1024 ≤ 1024 * (j * q) ∨
      1024 * (j * q) + 2048 ≤ 1024 * (lane * q + column) := by
  by_cases lt : lane < j
  · have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  · by_cases gt : j < lane
    · have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lane by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    · have eq : lane = j := by omega
      subst lane
      have large : 2 ≤ column := other.elim (fun h => False.elim (h rfl)) id
      omega

theorem initialized_zero (m : Mem) (base : Addr) (lanes q : Nat)
    (bound : 1024 * (lanes * q) < 2 ^ 64) (h0 : List Byte) :
    Initialized (clearMem m base (128 * (lanes * q))) base lanes q 0 h0 := by
  intro lane hl column hc
  rw [clearMem_block _ _ _ _ bound (cell_bound _ _ _ _ hl hc)]
  simp only [Nat.not_lt_zero, false_and, ite_false]

theorem initialized_lane {s t : State} (memory : Addr) (lanes q j : Nat)
    (h0 : List Byte) (space : Space s memory (1024 * (lanes * q)))
    (hq : 2 ≤ q) (hj : j < lanes) (lanesBound : lanes < 2 ^ 64)
    (dst : s.gpr .x22 = memory + BitVec.ofNat 64 (1024 * (j * q)))
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 j)
    (hash : bytesAt s.mem (s.gpr .x19) 64 = h0)
    (initialized : Initialized s.mem memory lanes q j h0) (done : LaneDone s t) :
    Initialized t.mem memory lanes q (j + 1) h0 := by
  have laneValue : (s.gpr .x20).toNat = j := by
    rw [laneReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have currentEnd : 1024 * (j * q) + 2048 ≤ 2 ^ 64 := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    have b := space.bound
    omega
  have cellEnd (lane column : Nat) (hl : lane < lanes) (hc : column < q) :
      1024 * (lane * q + column) + 1024 ≤ 2 ^ 64 := by
    have cell := cell_bound lanes q lane column hl hc
    have b := space.bound
    omega
  intro lane hl column hc
  by_cases same : lane = j
  · subst lane
    by_cases first : column = 0
    · subst column
      rw [ite_eq_left (by omega)]
      apply Proof.Argon2.blockAt_of_initialBytes
      have eq := done.first
      rw [hash, laneValue, dst] at eq
      simpa only [Nat.add_zero] using eq
    · by_cases second : column = 1
      · subst column
        rw [ite_eq_left (by omega)]
        apply Proof.Argon2.blockAt_of_initialBytes
        have eq := done.second
        rw [hash, laneValue, dst, BitVec.add_assoc,
          show (1024 : Addr) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add] at eq
        rw [Nat.mul_add, Nat.mul_one]
        exact eq
      · have large : 2 ≤ column := by omega
        have sep := cell_sep q j j column hq hc (Or.inr large)
        have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) =
            blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) := by
          apply blockAt_frame done.frame
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [dst]; exact Offset.disjoint _ sep (cellEnd j column hj hc) currentEnd
          · exact space.matrixWork.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega)) |>.sub_right
              (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
        rw [kept, initialized j hj column hc]
        simp only [Nat.lt_irrefl, false_and, ite_false, ite_eq_right (by omega : ¬ (j < j + 1 ∧ column < 2))]
  · have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) =
        blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) := by
      apply blockAt_frame done.frame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [dst]
        exact Offset.disjoint _ (cell_sep q j lane column hq hc (Or.inl same))
          (cellEnd lane column hl hc) currentEnd
      · exact space.matrixWork.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega)) |>.sub_right
          (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
    rw [kept, initialized lane hl column hc]
    by_cases before : lane < j ∧ column < 2 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.Argon2.AArch64.MemoryInit
