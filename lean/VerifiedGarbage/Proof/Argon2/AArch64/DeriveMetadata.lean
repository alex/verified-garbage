import VerifiedGarbage.Proof.Argon2.AArch64.DerivePrologue
import VerifiedGarbage.Proof.Argon2.AArch64.Parameters

/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_stack_word {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (j : Nat) (hj : j < 10) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (copyDestination j)) 64 =
      let word := abiWord s (8 * j)
      if j < 1 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ arguments) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold argumentValue
  unfold prologueState
  rw [frameStart_reg s _ arg.2]

theorem private_local_write {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem private_local_read {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Parameters.Ready (abiParams s) t := by
  refine ⟨private_local_read prepared 176 8 (by decide), private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := private_argument_word prepared (176, .x6) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      (((s.gpr .x6).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((s.gpr .x6).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := private_argument_word prepared (184, .x7) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      (((s.gpr .x7).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((s.gpr .x7).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.AArch64.Derive
