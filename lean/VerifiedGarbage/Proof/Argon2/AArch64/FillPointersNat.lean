import VerifiedGarbage.Proof.Argon2.AArch64.FillPointers
import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.FillPositions

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.AArch64.FillPointers

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillPointers

def cell (base : Addr) (p : Spec.Argon2.Params) (lane column : Nat) : Addr :=
  off base ((lane * p.laneLen + column) * 1024)

theorem address_nat (base : Addr) (lane column q : Nat) :
    address base (BitVec.ofNat 64 lane) (BitVec.ofNat 64 column) (BitVec.ofNat 64 q) =
      off base ((lane * q + column) * 1024) := by
  unfold address off
  change (BitVec.ofNat 64 lane * BitVec.ofNat 64 q + BitVec.ofNat 64 column) *
    BitVec.ofNat 64 1024 + base = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (rl : s.gpr .x5 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .x0 = BitVec.ofNat 64 refColumn) :
    WP isa code s fun t =>
      t.gpr .x6 = cell (s.gpr .x4) p lane (slice * p.segmentLen + index) ∧
      t.gpr .x0 = cell (s.gpr .x4) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .x1 = cell (s.gpr .x4) p refLane refColumn ∧ Divide.Keeps changed s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨current, previous, reference, keeps⟩
  have col : column s = BitVec.ofNat 64 (slice * p.segmentLen + index) := by
    unfold column
    rw [position.slice, position.segmentLength, position.index, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  have prev : predecessor s = BitVec.ofNat 64
      ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) := by
    unfold predecessor
    rw [col, position.laneLength]
    have positive := Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum
    have q := Proof.Argon2.laneLen_segments p bounds.lanesPositive
    exact FillColumn.previous_word_nat _ _ (by omega)
      (Nat.lt_trans bounds.laneLength_bound (by decide))
      (Proof.Argon2.column_lt p bounds.lanesPositive bounds.sliceBound bounds.indexBound)
  refine ⟨?_, ?_, ?_, keeps⟩
  · rw [current, position.current, col, position.laneLength, address_nat]; rfl
  · rw [previous, position.current, prev, position.laneLength, address_nat]; rfl
  · rw [reference, rl, rc, position.laneLength, address_nat]; rfl

end VG.Proof.Argon2.AArch64.FillPointers
