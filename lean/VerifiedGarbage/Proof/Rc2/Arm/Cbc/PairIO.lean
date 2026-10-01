import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Call
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # Pair loads and stores for 64-bit CBC blocks -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem halves {rs : List Region} {p : Addr} (h : InRegions rs p 8) :
    InRegions rs p 4 ∧ InRegions rs (p + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  constructor
  · exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  · refine ⟨r, hr, ?_⟩
    unfold Region.Contains at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add]
    have bound := Nat.mod_le ((p - r.base).toNat + (BitVec.ofNat 64 4).toNat) (2 ^ 64)
    change ((p - r.base).toNat + 4) % 2 ^ 64 + 4 ≤ r.len
    change ((p - r.base).toNat + 4) % 2 ^ 64 ≤ (p - r.base).toNat + 4 at bound
    omega

theorem loadPair_ok (s : State) (lo hi src : Reg) (a : Nat)
    (different : lo ≠ hi) (sep : src ≠ lo) (bound : a + 4 < 4096)
    (fit : (s.gpr src).toNat + a + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 a) 8) :
    ∃ s', runBlock isa [.ldr lo src a, .ldr hi src (a + 4)] s = some s' ∧
      s'.gpr lo = s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32 ∧
      s'.gpr hi = s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 (a + 4)) 32 ∧
      Keep [lo, hi] s s' := by
  obtain ⟨rd0, rd4⟩ := halves readable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at rd4
  rw [runBlock_cons, exec_ldr s lo src a (by omega) (by omega) rd0, runStep_some]
  have rd4' : InRegions ((s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).rd ++
      (s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).wr)
      (State.addr ((s.setReg lo (s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 a) 32)).gpr src) +
        BitVec.ofNat 64 (a + 4)) 4 := by
    simpa only [rd_setReg, wr_setReg, gpr_setReg_of_ne _ _ sep] using rd4
  rw [runBlock_cons, exec_ldr _ hi src (a + 4) bound
    (by rw [gpr_setReg_of_ne _ _ sep]; omega) rd4', runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [gpr_setReg_of_ne _ _ different, gpr_setReg_self]
  · rw [gpr_setReg_self, gpr_setReg_of_ne _ _ sep, mem_setReg]
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gpr_setReg_of_ne _ _ hr.2, gpr_setReg_of_ne _ _ hr.1]

theorem storePair_ok (s : State) (lo hi dst : Reg) (b : Nat) (bound : b + 4 < 4096)
    (fit : (s.gpr dst).toNat + b + 8 ≤ 2 ^ 32)
    (writable : InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 b) 8) :
    ∃ s', runBlock isa [.str lo dst b, .str hi dst (b + 4)] s = some s' ∧
      Keep [] {s with
        mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b)
          (s.gpr hi ++ s.gpr lo)} s' := by
  obtain ⟨wr0, wr4⟩ := halves writable
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at wr4
  rw [runBlock_cons, exec_str s lo dst b (by omega) (by omega) wr0, runStep_some,
    runBlock_cons, exec_str {s with mem := s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 b) (s.gpr lo)} hi dst (b + 4) bound (by change (s.gpr dst).toNat + (b + 4) < 2 ^ 32; omega) wr4,
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun _ _ => rfl, ?_, rfl, rfl⟩
  rw [write64_pair, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Rc2.Arm.Cbc
