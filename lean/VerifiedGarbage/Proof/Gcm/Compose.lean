import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# GCM: the streaming state, the tag and the pre-counter block

Untrusted: everything here is checked by Lean. Target-independent lemmas
relating the steps of `Stream.lean` and `Ctr.lean` to `StreamRepr`,
`fullTag` and `j0`:

* `streamRepr_iff`: the state is `J₀`, GHASH having absorbed
  `ghashInput a c` (`Absorbed`) and the counter state after `len(C)` bytes
  (`Ctr`).
* `ghashInput_append`: more text, after the additional data padded (if it
  is the first text).
* `fullTag_eq`: the tag from GHASH having absorbed `ghashInput a c` padded
  with zeros, then the lengths block, XORed with `CIPH_K(J₀)`.
* `j0_eq`: `J₀` for an IV other than 12 bytes is GHASH having absorbed the IV
  padded, then the lengths block of no additional data and the IV.
* `inc32_bytes`: `inc₃₂` increments the last four bytes, big-endian.
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

theorem streamRepr_iff {m : Mem} {p : Addr} {ciph : Block → Block} {h : Block} {iv a c : List Byte} :
    StreamRepr m p ciph h iv a c ↔
      blockAt m p = j0 h iv ∧ Absorbed m (p + 16) (p + 32) h (ghashInput a c) ∧
        Ctr m (p + 48) (p + 64) ciph (inc32 (j0 h iv)) c.length := by
  simp only [StreamRepr, Absorbed, Ctr, whole, and_assoc]

/-! ## What GHASH absorbs -/

theorem ghashInput_nil (a : List Byte) : ghashInput a [] = a := rfl

theorem ghashInput_of_ne {a c : List Byte} (hc : c ≠ []) :
    ghashInput a c = a ++ zeros (padLen a.length) ++ c := by simp [ghashInput, hc]

/-- More text: the additional data padded first, if there was no text. -/
theorem ghashInput_append (a c e : List Byte) (he : e ≠ []) :
    ghashInput a (c ++ e) = (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c) ++ e := by
  have hce : c ++ e ≠ [] := by simp [he]
  rw [ghashInput_of_ne hce]
  split
  · next h => subst h; rfl
  · next h => rw [ghashInput_of_ne h]; simp only [List.append_assoc]

theorem length_pad_mod (n : Nat) : (n + padLen n) % 16 = 0 := by simp only [padLen]; omega

/-- The lengths block `[len(A)]₆₄ ‖ [len(C)]₆₄`. -/
def lensBlock (aLen cLen : Nat) : List Byte := be64 (8 * aLen) ++ be64 (8 * cLen)

theorem length_be64 (x : Nat) : (be64 x).length = 8 := by simp [be64]

theorem length_lensBlock (aLen cLen : Nat) : (lensBlock aLen cLen).length = 16 := by
  simp [lensBlock, length_be64]

/-- `ghashInput a c` padded with zeros to a whole number of blocks. -/
def padded (a c : List Byte) : List Byte :=
  ghashInput a c ++ zeros (padLen (ghashInput a c).length)

theorem length_padded (a c : List Byte) : (padded a c).length % 16 = 0 := by
  simp only [padded, List.length_append, length_zeros]; exact length_pad_mod _

/-- `S`'s blocks: the padded input, then the lengths block. -/
theorem authBlocks_eq (a c : List Byte) :
    authBlocks a c = blocks (padded a c) ++ [ofBytes (lensBlock a.length c.length)] := by
  rw [← blocks_single (length_lensBlock _ _), ← blocks_append (length_padded a c)]
  unfold authBlocks padded lensBlock
  by_cases hc : c = []
  · subst hc; simp [ghashInput_nil, zeros, padLen]
  · rw [ghashInput_of_ne hc]
    have : padLen (a ++ zeros (padLen a.length) ++ c).length = padLen c.length := by
      simp only [List.length_append, length_zeros, padLen]; omega
    rw [this]; simp only [List.append_assoc]

/-- GHASH having absorbed a whole number of blocks. -/
theorem Absorbed.whole_eq {m : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : Absorbed m y b h x)
    (h0 : x.length % 16 = 0) : blockAt m y = ghash h (blocks x) := by
  rw [hx.1, List.take_of_length_le (by rw [whole_of_mod h0])]

/-- The tag: GHASH of the padded input continued over the lengths block,
XORed with `CIPH_K(J₀)`. -/
theorem fullTag_eq (ciph : Block → Block) (h : Block) (iv a c : List Byte) :
    fullTag ciph h iv a c =
      toBytes (ghashFrom h (ghash h (blocks (padded a c))) [ofBytes (lensBlock a.length c.length)] ^^^
        ciph (j0 h iv)) := by
  rw [fullTag, gctr_block, authBlocks_eq, ghash, ghashFrom_append]; rfl

/-! ## The pre-counter block -/

theorem be64_zero : be64 0 = zeros 8 := by decide

/-- `J₀` for an IV other than 12 bytes: GHASH of the IV padded, then of the
lengths block for no additional data and an IV of `len(IV)` bytes. -/
theorem j0_eq (h : Block) {iv : List Byte} (hiv : iv.length ≠ 12) :
    j0 h iv = ghashFrom h (ghash h (blocks (iv ++ zeros (padLen iv.length))))
      [ofBytes (lensBlock 0 iv.length)] := by
  have hz : zeros (padLen iv.length + 8) = zeros (padLen iv.length) ++ zeros 8 := by
    rw [zeros, zeros, zeros, List.replicate_append_replicate]
  simp only [j0, hiv, ↓reduceIte]
  rw [hz, ← List.append_assoc, List.append_assoc _ (zeros 8),
    blocks_append (by simp only [List.length_append, length_zeros]; exact length_pad_mod _),
    ghash, ghashFrom_append, lensBlock, Nat.mul_zero, be64_zero, blocks_single (bs := zeros 8 ++ be64 (8 * iv.length)) (by simp [length_be64, zeros])]
  rfl

/-- `J₀` for a 12-byte IV. -/
theorem j0_12 (h : Block) {iv : List Byte} (hiv : iv.length = 12) :
    j0 h iv = ofBytes (iv ++ [0, 0, 0, 1]) := by simp only [j0, hiv, ↓reduceIte]

end VG.Proof.Gcm
