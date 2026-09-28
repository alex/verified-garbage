import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# GCM blocks in SSE registers

Untrusted: everything here is checked by Lean. A 16-byte load puts the
first byte in the least significant byte of the register (`byte_readW`);
`pshufb` with the byte-reversal mask `revMask` turns it into the block's
value as SP 800-38D reads it, the first byte the most significant
(`blockAt_eq`), and back (`blockAt_store`).
-/

namespace VG.Proof.Gcm.X86_64

open VG.X86_64

/-- The `pshufb` mask that reverses the 16 bytes. -/
abbrev revMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128

theorem pshufb_rev (a : BitVec 128) :
    XBinOp.eval .pshufb a revMask = ofBytes fun i => byte a (15 - i) := by
  simp only [XBinOp.eval, ofBytes]; rfl

theorem byte_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byte (ofBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofBytes f hi hr

theorem ext_byte {a b : BitVec 128} (h : ∀ i < 16, byte a i = byte b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (BitVec.getLsbD · (j % 8)) (h (j / 8) (by omega))
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt j (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem byte_readW (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    byte (m.readW p 128) i = m (p + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m p (n := 16) hi]
  simp only [byte, Mem.readW]
  rfl

theorem pshufb_rev_rev (a : BitVec 128) :
    XBinOp.eval .pshufb (XBinOp.eval .pshufb a revMask) revMask = a := by
  apply ext_byte; intro i hi
  rw [pshufb_rev, byte_ofBytes _ hi, pshufb_rev, byte_ofBytes _ (by omega)]
  exact congrArg _ (by omega)

/-- The block at `p`, loaded and byte-reversed. -/
theorem blockAt_eq (m : Mem) (p : Addr) :
    Spec.Gcm.blockAt m p = XBinOp.eval .pshufb (m.readW p 128) revMask := by
  rw [pshufb_rev]
  have e : ∀ k, k < 16 → byte (m.readW p 128) k = m (p + BitVec.ofNat 64 k) :=
    fun k hk => byte_readW m p hk
  simp only [ofBytes, Nat.reduceSub, e 0 (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
    e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega),
    e 14 (by omega), e 15 (by omega)]
  rw [Spec.Gcm.blockAt, show Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] from rfl, ofBytes_16]
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_append]
  generalize m (p + BitVec.ofNat 64 0) = b0
  generalize m (p + BitVec.ofNat 64 1) = b1
  generalize m (p + BitVec.ofNat 64 2) = b2
  generalize m (p + BitVec.ofNat 64 3) = b3
  generalize m (p + BitVec.ofNat 64 4) = b4
  generalize m (p + BitVec.ofNat 64 5) = b5
  generalize m (p + BitVec.ofNat 64 6) = b6
  generalize m (p + BitVec.ofNat 64 7) = b7
  generalize m (p + BitVec.ofNat 64 8) = b8
  generalize m (p + BitVec.ofNat 64 9) = b9
  generalize m (p + BitVec.ofNat 64 10) = b10
  generalize m (p + BitVec.ofNat 64 11) = b11
  generalize m (p + BitVec.ofNat 64 12) = b12
  generalize m (p + BitVec.ofNat 64 13) = b13
  generalize m (p + BitVec.ofNat 64 14) = b14
  generalize m (p + BitVec.ofNat 64 15) = b15
  omega

/-- SP 800-38D's block of 16 bytes (the first the most significant) is the
register holding them in reverse order. -/
theorem gcmOfBytes_eq (f : Nat → BitVec 8) :
    Spec.Gcm.ofBytes ((List.range 16).map f) = ofBytes fun i => f (15 - i) := by
  rw [show (List.range 16).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11,
    f 12, f 13, f 14, f 15] from rfl, ofBytes_16]
  apply BitVec.eq_of_toNat_eq
  simp only [ofBytes, toNat_append, Nat.reduceSub]
  generalize f 0 = b0
  generalize f 1 = b1
  generalize f 2 = b2
  generalize f 3 = b3
  generalize f 4 = b4
  generalize f 5 = b5
  generalize f 6 = b6
  generalize f 7 = b7
  generalize f 8 = b8
  generalize f 9 = b9
  generalize f 10 = b10
  generalize f 11 = b11
  generalize f 12 = b12
  generalize f 13 = b13
  generalize f 14 = b14
  generalize f 15 = b15
  omega

/-- The register of a block `x` loaded as bytes: byte `i` is byte `15 - i` of `x`. -/
theorem byte_pshufb_rev (x : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (XBinOp.eval .pshufb x revMask) i = byte x (15 - i) := by
  rw [pshufb_rev, byte_ofBytes _ hi]

theorem pshufb_rev_xor (a b : BitVec 128) :
    XBinOp.eval .pshufb (a ^^^ b) revMask =
      XBinOp.eval .pshufb a revMask ^^^ XBinOp.eval .pshufb b revMask := by
  apply ext_byte; intro i hi
  have bx : ∀ (x y : BitVec 128) (j : Nat), byte (x ^^^ y) j = byte x j ^^^ byte y j := by
    intro x y j
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hk, decide_true, Bool.true_and]
  rw [bx, byte_pshufb_rev _ hi, byte_pshufb_rev _ hi, byte_pshufb_rev _ hi, bx]

/-- A block, byte-reversed and stored at `p`. -/
theorem blockAt_store (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Gcm.blockAt (m.writeW p (XBinOp.eval .pshufb v revMask)) p = v := by
  rw [blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide), pshufb_rev_rev]

end VG.Proof.Gcm.X86_64
