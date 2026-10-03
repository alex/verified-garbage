import VerifiedGarbage.Proof.Argon2.X86.Rounds
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 on x86 (32-bit): blocks as 32-bit words

A block at `B + o` (`blk m B o`) as 64-bit words, each the pair of 32-bit words
the code copies: `blk_of_words` builds it from them, `blockAt_eq` relates it to
the contract's `Spec.Argon2.blockAt`, and `xor_words` XORs two blocks word by
word.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (rd64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_append hi_append eq_of_lo_hi)

/-- The block at `B + o`, as pairs of 32-bit words. -/
def blk (m : Mem) (B : BitVec 32) (o : Nat) : Block := Vector.ofFn fun j => rd64 m B (o + 8 * j.val)

/-- The block made of the 32-bit words `f 0, f 1, …` (two per 64-bit word, the low one first). -/
def ofWords (f : Nat → BitVec 32) : Block := Vector.ofFn fun j => f (2 * j.val + 1) ++ f (2 * j.val)

theorem blk_of_words {m : Mem} {B : BitVec 32} {o : Nat} {f : Nat → BitVec 32}
    (h : ∀ i < 256, m.readW (addr B (o + 4 * i)) 32 = f i) : blk m B o = ofWords f := by
  apply Vector.ext
  intro j hj
  simp only [blk, ofWords, Vector.getElem_ofFn, rd64]
  rw [show o + 8 * j + 4 = o + 4 * (2 * j + 1) by omega, show o + 8 * j = o + 4 * (2 * j) by omega,
    h _ (by omega), h _ (by omega)]

theorem working_eq (m : Mem) (B : BitVec 32) : working m B = blk m B 1024 := by
  apply Vector.ext
  intro j hj
  simp only [working, blk, Vector.getElem_ofFn, Impl.Argon2.X86.wOff]

theorem blockAt_eq {m : Mem} {B : BitVec 32} (hfit : B.toNat + 1024 ≤ 2 ^ 32) :
    blockAt m (B.setWidth 64) = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, blk, Vector.getElem_ofFn, Nat.zero_add]
  rw [Proof.Blake2.X86.CompressB.rd64_eq (by omega)]
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem append_xor (a b c d : BitVec 32) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  eq_of_lo_hi (by rw [lo_xor, lo_append, lo_append, lo_append])
    (by rw [hi_xor, hi_append, hi_append, hi_append])

theorem xor_words (f g : Nat → BitVec 32) :
    xorBlock (ofWords f) (ofWords g) = ofWords fun i => f i ^^^ g i := by
  apply Vector.ext
  intro j hj
  simp only [xorBlock, ofWords, Vector.getElem_zipWith, Vector.getElem_ofFn, append_xor]

/-- A prefix of `n` 32-bit words at `B + o` holds `f`. -/
def Words (m : Mem) (B : BitVec 32) (o : Nat) (f : Nat → BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, m.readW (addr B (o + 4 * i)) 32 = f i

end VG.Proof.Argon2.X86
