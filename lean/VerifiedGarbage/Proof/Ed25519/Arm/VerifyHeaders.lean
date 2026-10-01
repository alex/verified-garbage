import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyContext

/-! Untrusted: load a public argument pointer from the protected header area. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem loadHeader_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (d : Nat) (hd : d + 4 ≤ 8192) :
    WP isa (.block (loadHeader d)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  unfold loadHeader
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc d (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 d) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by omega)))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) hd (by omega))
    fun t ht => WP.block_nil ⟨ur.trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

theorem addInput32_ok (s : State) :
    WP isa (.block [.dp .add .r12 .r12 (.imm 32)]) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.gpr .r12 + 32 := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.Arm
