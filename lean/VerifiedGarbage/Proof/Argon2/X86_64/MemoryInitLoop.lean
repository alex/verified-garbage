import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitFrame

/-! # Termination and correctness of the all-lanes initialization loop -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopI (s₀ : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte) (s : State) : Prop where
  bound : j ≤ lanes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 (1024 * (j * q))
  lane : s.gpr .r12 = BitVec.ofNat 64 j
  remaining : s.gpr .r15 = BitVec.ofNat 64 (lanes - j)
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  keeps : Keeps s₀ s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q j h0
  hash : bytesAt s.mem (s.gpr .rbp) 64 = h0

theorem lanesLoop_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₀ : State) (memory : Addr) (lanes q : Nat) (h0 : List Byte)
    (space : Space s₀ memory (1024 * (lanes * q))) (lo : 1 ≤ lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (dst : s₀.gpr .r14 = memory) (laneReg : s₀.gpr .r12 = 0)
    (remaining : s₀.gpr .r15 = BitVec.ofNat 64 lanes)
    (stride : s₀.gpr .r13 = BitVec.ofNat 64 (1024 * q))
    (initialized : Initialized s₀.mem memory lanes q 0 h0)
    (hash : bytesAt s₀.mem (s₀.gpr .rbp) 64 = h0) :
    WP isa (.loop (lane name (HPrime.hash v)) .ne) s₀ (LoopI s₀ memory lanes q lanes h0) := by
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = lanes - j ∧ j < lanes ∧ LoopI s₀ memory lanes q j h0 s)
    ?_ lanes s₀ ⟨0, by omega, lo, by omega, by simpa using dst, laneReg,
      by simpa only [Nat.sub_zero] using remaining, stride, Keeps.refl _ _ _, initialized, hash⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have spaceS := space.keeps h.keeps
  have endBound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  refine (lane_ok v name s memory (1024 * (lanes * q)) (1024 * (j * q))
    spaceS h.destination endBound).mono ?_
  intro t ht
  have kt := ht.keeps memory _ _ h.destination endBound
  have nextCount : BitVec.ofNat 64 (lanes - j) - 1 = BitVec.ofNat 64 (lanes - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : LoopI s₀ memory lanes q (j + 1) h0 t := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, h.keeps.trans kt,
      initialized_lane memory lanes q j h0 spaceS hq hj lanesBound h.destination h.lane
        h.hash h.initialized ht, (kt.h0 spaceS).trans h.hash⟩
    · rw [ht.destination, h.destination, h.stride, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_mul, Nat.one_mul, Nat.mul_add]
    · rw [ht.lane, h.lane, BitVec.ofNat_add]; rfl
    · rw [ht.remaining, h.remaining, nextCount]
    · exact (kt.regs .r13 (by decide)).trans h.stride
  have zf : t.zf = some (decide (lanes - (j + 1) = 0)) := by
    rw [ht.zf, h.remaining, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lanes - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  by_cases done : j + 1 = lanes
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show lanes - (j + 1) = 0 by omega, decide_true,
      Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, lanes - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, zf, show lanes - (j + 1) ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.MemoryInit
