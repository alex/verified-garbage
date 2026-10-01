import VerifiedGarbage.Impl.Ed25519.Arm.PointMul
import VerifiedGarbage.Proof.Ed25519.Arm.MulKeep

/-! Untrusted: the public descending batch counter is saved across field operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem counterStore_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat)
    (hv : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [.str .r11 .r0 56]) s fun t => Rest [] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine str0_ok hc (by decide) fun t ht => WP.block_nil ⟨ht.rest _, ?_, ?_⟩
  · rw [ht.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [ht.mem, Mem.readW_writeW_self32, hv]

theorem MulKeep.of_counter {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

theorem batchStart_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1)) :
    WP isa (.block batchStart) s fun t => Rest [.r11] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 j ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine ldr0_ok hc (by decide) fun u hu => wp_dp (op2_imm (by decide)) fun v hv' => ?_
  have ev : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hv'.gpr]
    change u.gpr .r11 - 1 = _
    rw [hu.gpr, hv, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have rv : Rest [.r11] s v := (hu.rest (by decide)).trans (hv'.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv'.mem, hu.mem]
  refine WP.mono (counterStore_ok (hc.of_rest rv (by decide)) j ev) fun t ⟨tr, tf, tv⟩ => ?_
  exact ⟨rv.trans (tr.mono (by decide)), by rw [← mv]; exact tf,
    (tr.gpr _ (by decide)).trans ev, tv⟩

theorem batchTest_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat) (hj : j < 32)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j) :
    WP isa (.block batchTest) s fun t => Rest [.r11] s t ∧ t.mem = s.mem ∧ t.z = decide (j = 0) := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  have he : BitVec.ofNat 32 j - (0 : BitVec 32) = BitVec.ofNat 32 j := BitVec.sub_zero _
  rw [hz, hu.gpr, hv, he, ofNat_beq_zero (by omega)]

end VG.Proof.Ed25519.Arm
