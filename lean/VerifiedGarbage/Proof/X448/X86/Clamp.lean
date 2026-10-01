import VerifiedGarbage.Proof.X448.X86.BitWrite

/-!
# X448 on x86 (32-bit): clamping the scalar bits

Untrusted: everything here is checked by Lean. Clear bits zero and one,
and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def clamp : List Instr :=
  [.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl,
    .mov .edx (.imm 1), .store8 (sc (BITS + 447)) .dl]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.store8 (sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .edx).setWidth 8) ∧ Keeps [] s t := by
  refine wp_store8 (hs.ea (d := d) (by omega)) (hs.write (d := d) (n := 1) (by omega))
    fun t ht => WP.block_nil ⟨ht.mem, (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) :
    WP isa (.block [.mov .edx (.imm v), .store8 (sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .edx = v ∧ Keeps [.edx] s t := by
  refine wp_mov rfl fun t ht => ?_
  refine WP.mono (storeByte_ok (hs.of_upd ht (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    ((ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.edx] s t := by
  change WP isa (.block (([.mov .edx (.imm 0), .store8 (sc BITS) .dl] : List Instr) ++
    ([.store8 (sc (BITS + 1)) .dl] : List Instr) ++
    [.mov .edx (.imm 1), .store8 (sc (BITS + 447)) .dl])) s _
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

end VG.Proof.X448.X86
