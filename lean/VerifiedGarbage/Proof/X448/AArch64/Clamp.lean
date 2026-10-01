import VerifiedGarbage.Proof.X448.AArch64.BitWrite

/-!
# X448 on AArch64: clamping the scalar bits

Untrusted: everything here is checked by Lean. Clear bits zero and one,
and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def clamp : List Instr :=
  [.movz .x .x4 0 0, .strb .x4 .x3 BITS, .strb .x4 .x3 (BITS + 1),
    .movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .x4).setWidth 8) ∧ Keeps [] s t := by
  have w := hs.write (d := d) (n := 1) (by omega)
  have enc : d % 1 = 0 ∧ d < 4096 := ⟨by omega, hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self,
    hs.x3, State.store, w, State.read, ite_true, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl⟩
  rw [write1_eq]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Size.bits]
  omega

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 16) :
    WP isa (.block [.movz .x .x4 v 0, .strb .x4 .x3 d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .x4 = v.setWidth 64 ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 v 0] : List Instr) ++ [.strb .x4 .x3 d])) s _
  rw [WP.block_append_iff]
  have set : WP isa (.block [.movz .x .x4 v 0]) s fun t =>
      t.gpr .x4 = v.setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono set fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, (uk.1 _ (by decide)).trans tv, tk.trans (uk.mono (by simp))⟩
  rw [um, tm, tv]
  apply congrArg (s.mem.writeW (off base d))
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.x4] s t := by
  change WP isa (.block (([.movz .x .x4 0 0, .strb .x4 .x3 BITS] : List Instr) ++
    ([.strb .x4 .x3 (BITS + 1)] : List Instr) ++
    [.movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hs (by decide : BITS < 4096) 0) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.AArch64
