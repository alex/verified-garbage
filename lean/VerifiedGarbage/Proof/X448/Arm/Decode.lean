import VerifiedGarbage.Proof.X448.Arm.Swap
import VerifiedGarbage.Proof.X448.Radix16Bytes

/-!
# X448 on ARMv7: decoding a coordinate limb

Untrusted: everything here is checked by Lean. Two byte loads construct a
16-bit limb, which is written to both initial coordinate slots.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_ldrb wp_dp op2_lsl)

theorem decodeLimb_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat}
    (hi : i < 28) (hp : State.addr (s.gpr .r2) = p) (hfit : (s.gpr .r2).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1) :
    WP isa (.block (decodeLimb i)) s fun t =>
      t.mem = (s.mem.writeW (off base (X1 + 4 * i)) (BitVec.ofNat 32 (decoded s.mem p i))).writeW
        (off base (X3 + 4 * i)) (BitVec.ofNat 32 (decoded s.mem p i)) ∧ Keeps [.r3, .r4] s t := by
  have ea0 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * i)) = off p (2 * i) := by
    rw [addr_add (by omega), hp]
  have ea1 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * i + 1)) = off p (2 * i + 1) := by
    rw [addr_add (by omega), hp]
  unfold decodeLimb
  refine wp_ldrb (a := off p (2 * i)) (by omega) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_ldrb (a := off p (2 * i + 1)) (by omega)
    (by rw [h1.other .r2 (by decide)]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 h3 => ?_
  have value : s3.gpr .r3 = BitVec.ofNat 32 (decoded s.mem p i) := by
    rw [h3.gpr]
    change s2.gpr .r3 + s2.gpr .r4 <<< 8 = _
    rw [h2.other .r3 (by decide), h1.gpr, h2.gpr, h1.mem]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (off p (2 * i))).isLt
    have h1 := (s.mem (off p (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, decoded, byteN]
    simp only [off] at h0 h1 ⊢
    omega
  have hs1 := hs.of_upd h1 (by decide) (by decide)
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  have hs3 := hs2.of_upd h3 (by decide) (by decide)
  refine store_ok hs3 (by simp only [X1, slot]; omega) fun s4 h4 => ?_
  have hs4 := hs3.of_keeps (rest_keeps (h4.rest [])) (by decide)
  refine store_ok hs4 (by simp only [X3, slot]; omega) fun s5 h5 => WP.block_nil ⟨?_, ?_⟩
  · rw [h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h4.gpr, value]
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((h3.rest (by decide)).trans ((h4.rest _).trans (h5.rest _)))))

/-- The two coordinate words lie inside their respective slots. -/
theorem decodeLimb_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    Outside2 base X1 (4 * (i + 1)) X3 (4 * (i + 1)) m
      ((m.writeW (off base (X1 + 4 * i)) v).writeW (off base (X3 + 4 * i)) v) := by
  intro p hp hq
  rw [writeW_outside _ _ _ (by simp only [X3, slot]; omega) p (by omega),
    writeW_outside _ _ _ (by simp only [X1, slot]; omega) p (by omega)]

end VG.Proof.X448.Arm
