import VerifiedGarbage.Proof.X448.Arm.BitWrite

/-!
# X448 on ARMv7: clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def clamp : List Instr :=
  [.mov .r3 (.imm 0), .strb .r3 .r0 BITS, .strb .r3 .r0 (BITS + 1),
    .mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .r3).setWidth 8) ∧ Keeps [] s t := by
  refine VG.Proof.X25519.Arm.wp_strb hd (hs.ea (by omega)) (hs.write (by omega))
    fun t ht => WP.block_nil ⟨ht.mem, rest_keeps (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) (hv : encodable v = true) :
    WP isa (.block [.mov .r3 (.imm v), .strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .r3 = v ∧ Keeps [.r3] s t := by
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm hv) fun t ht => ?_
  refine WP.mono (storeByte_ok (hs.of_upd ht (by decide) (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    (rest_keeps (ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.r3] s t := by
  change WP isa (.block (([.mov .r3 (.imm 0), .strb .r3 .r0 BITS] : List Instr) ++
    ([.strb .r3 .r0 (BITS + 1)] : List Instr) ++
    [.mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hs (by decide : BITS < 4096) 0 (by decide)) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1 (by decide)) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.Arm
