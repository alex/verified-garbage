import VerifiedGarbage.Proof.X448.X86.RowMem

/-!
# X448 on x86 (32-bit): advancing the product row

The last carry becomes the next product word, and the public row pointer
controls loop termination.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def rowTail : List Instr :=
  [.store (at_ .ebp (ACC + 112)) .ebx, .alu .add .ebp (.imm 4),
    .mov .edx (.reg .edi), .alu .add .edx (.imm 112), .alu .cmp .ebp (.reg .edx)]

theorem rowTail_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block rowTail) s fun t =>
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = 28)) ∧
      t.mem = s.mem.writeW (off base (ACC + 4 * (i + 28))) (s.gpr .ebx) ∧ Keeps clob s t := by
  have ea : s.ea (at_ .ebp (ACC + 112)) = off base (ACC + 4 * (i + 28)) := by
    rw [rowEa hs hp (by simp only [ACC]; omega), show 4 * i + (ACC + 112) = ACC + 4 * (i + 28) by omega]
  unfold rowTail
  refine wp_store ea (hs.write (by simp only [ACC]; omega)) fun t ht => ?_
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine wp_mov rfl fun v hv => ?_
  refine wp_alu (Or.inl rfl) rfl fun w hw _ => ?_
  refine wp_cmp rfl fun x hx hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hx.gpr, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr]
    change t.gpr .ebp + BitVec.ofNat 32 4 = _
    rw [ht.gpr, hp, Offset.add_add, Nat.mul_succ,
      hw.other .edi (by decide), hv.other .edi (by decide), hu.other .edi (by decide), ht.gpr]
  · rw [hz, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr, hw.gpr]
    apply congrArg some
    change ((t.gpr .ebp + (4 : BitVec 32) - (v.gpr .edx + (112 : BitVec 32))) == 0) = _
    rw [hv.gpr, hu.other .edi (by decide), ht.gpr, hp]
    change ((s.gpr .edi + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 - (s.gpr .edi + BitVec.ofNat 32 112)) == 0) = _
    rw [Offset.add_add, Offset.add_sub_add_left]
    have check : ∀ n < 28, ((BitVec.ofNat 32 (4 * n + 4) - BitVec.ofNat 32 112) == 0) = decide (n + 1 = 28) := by decide
    exact check i hi
  · rw [hx.mem, hw.mem, hv.mem, hu.mem, ht.mem]
  · exact (ht.rest _).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      ((hw.rest (by decide)).trans (hx.rest _))))

end VG.Proof.X448.X86
