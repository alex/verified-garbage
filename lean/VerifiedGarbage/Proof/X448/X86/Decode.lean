import VerifiedGarbage.Proof.X448.X86.Swap
import VerifiedGarbage.Proof.X448.Radix16Bytes

/-!
# X448 on x86 (32-bit): decoding a coordinate limb

Two byte loads construct a 16-bit limb, which is written to both initial
coordinate slots.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
theorem byte_rotate (b : BitVec 8) : (b.setWidth 32).rotateRight 24 = b.setWidth 32 <<< 8 := by
  have hz : b.setWidth 32 >>> 24 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    change b.toNat % 2 ^ 32 / 2 ^ 24 = 0
    omega
  rw [BitVec.rotateRight_def, hz]
  exact BitVec.zero_or


theorem decodeLimb_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat}
    (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1) :
    WP isa (.block (decodeLimb i)) s fun t =>
      t.mem = (s.mem.writeW (off base (X1 + 4 * i)) (BitVec.ofNat 32 (decoded s.mem p i))).writeW
        (off base (X3 + 4 * i)) (BitVec.ofNat 32 (decoded s.mem p i)) ∧ Keeps [.eax, .edx] s t := by
  have ea0 : (s.gpr .esi + BitVec.ofNat 32 (2 * i)).setWidth 64 = off p (2 * i) := by
    change addr (s.gpr .esi) _ = _
    rw [VG.X86.addr_eq (by omega), hp]
  have ea1 : (s.gpr .esi + BitVec.ofNat 32 (2 * i + 1)).setWidth 64 = off p (2 * i + 1) := by
    change addr (s.gpr .esi) _ = _
    rw [VG.X86.addr_eq (by omega), hp]
  unfold decodeLimb
  refine wp_load8 (a := off p (2 * i)) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_load8 (a := off p (2 * i + 1))
    (by change addr (s1.gpr .esi) _ = _; rw [h1.other .esi (by decide)]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_shift (by decide) fun sr hrot => ?_
  refine wp_alu (by simp [plain]) rfl fun s3 h3 _ => ?_
  have value : s3.gpr .eax = BitVec.ofNat 32 (decoded s.mem p i) := by
    rw [h3.gpr]
    change sr.gpr .eax + sr.gpr .edx = _
    rw [hrot.other .eax (by decide), hrot.gpr]
    rw [h2.other .eax (by decide), h1.gpr, h2.gpr, h1.mem, byte_rotate]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (off p (2 * i))).isLt
    have h1 := (s.mem (off p (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, decoded, byteN]
    simp only [off] at h0 h1 ⊢
    omega
  have hs1 := hs.of_upd h1 (by decide)
  have hs2 := hs1.of_upd h2 (by decide)
  have hsrot := hs2.of_upd hrot (by decide)
  have hs3 := hsrot.of_upd h3 (by decide)
  refine store_ok hs3 (by simp only [X1, slot]; omega) fun s4 h4 => ?_
  have hs4 := hs3.of_keeps ((h4.rest [])) (by decide)
  refine store_ok hs4 (by simp only [X3, slot]; omega) fun s5 h5 => WP.block_nil ⟨?_, ?_⟩
  · rw [h5.mem, h4.mem, h3.mem, hrot.mem, h2.mem, h1.mem, h4.gpr, value]
  · exact ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((hrot.rest (by decide)).trans ((h3.rest (by decide)).trans ((h4.rest _).trans (h5.rest _))))))

/-- The two coordinate words lie inside their respective slots. -/
theorem decodeLimb_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    Outside2 base X1 (4 * (i + 1)) X3 (4 * (i + 1)) m
      ((m.writeW (off base (X1 + 4 * i)) v).writeW (off base (X3 + 4 * i)) v) := by
  intro p hp hq
  rw [writeW_outside _ _ _ (by simp only [X3, slot]; omega) p (by omega),
    writeW_outside _ _ _ (by simp only [X1, slot]; omega) p (by omega)]

end VG.Proof.X448.X86
