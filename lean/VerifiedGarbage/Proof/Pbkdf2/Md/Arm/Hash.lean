import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Compress
import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Init

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on ARMv7: the hash function

As on AArch64 (`Proof/Pbkdf2/Md/AArch64/Hash.lean`), `HashOK H` is what the
proofs know of the hash function whose code `H` describes: it is a
Merkle–Damgård hash function `md` (`Md`) whose digest code does what it should
(`OutOk`) and whose length field for a `B + D`-byte message is the constant
words the code stores (`len`), with a verified compression function
(`CompOk`); its streaming functions are verified against the contracts HMAC's
generic proofs call them with (`stream`); its specification is `md` from the
initial hash value `iv`, with the digest the first `D` bytes of `md`'s; and
its sizes fit (`Sizes`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash lenWords)
open Spec.Hmac (StreamingHash)

/-- The sizes the proofs support, checked for each hash function by
`decide`: words of 4 bytes, a digest of at most the hash value, room for the
padding in the block after the digest and after the hash value, the
streaming state as the hash value followed by a block, `finalize` writing
the whole hash value, and the compression function's scratch space within
the working space of the functions we call. -/
structure Sizes (H : Hash) : Prop where
  B : H.B = 64 ∨ H.B = 128
  N4 : H.N % 4 = 0
  D4 : H.D % 4 = 0
  L4 : H.L % 4 = 0
  D0 : 0 < H.D
  DN : H.D ≤ H.N
  NL : H.N + H.L ≤ H.B
  pad : H.D + 4 ≤ H.B - H.L
  N64 : H.N ≤ 64
  L16 : H.L ≤ 16
  so : H.so ≤ 8 * H.st.W
  W : H.st.W ≤ 64
  S : H.st.S = H.N + H.B
  F : H.st.F = H.N

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs see it. -/
  md : Md H.B H.N H.L
  out : OutOk md H.out
  /-- The compression function is verified. -/
  comp : CompOk md H.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The constant length field is that of a `B + D`-byte message. -/
  len : wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)
  /-- The streaming functions, verified. -/
  stream : Hmac.Generic.Arm.HashOK H.st
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m → md.Repr iv mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  sizes : Sizes H

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.N + H.B := hH.stream.hS.trans hH.sizes.S
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B_ge : 64 ≤ H.B := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B4 : H.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega

/-- The hash function of the specification is `md` from `iv`. -/
theorem link : hH.md.Link hH.SH hH.iv H.D :=
  ⟨hH.hB, hH.hS, hH.hD, hH.repr, hH.hash, hH.sizes.DN, by have := hH.sizes.pad; have := hH.sizes.NL; omega⟩

/-- The length field's bytes, as stored. -/
theorem lenBytes_eq : wordsBytes (lenWords H.be H.L (H.B + H.D)) = hH.md.lenBytes (H.B + H.D) := hH.len

theorem lenWords_length : (lenWords H.be H.L (H.B + H.D)).length = H.L / 4 := by simp [lenWords]

end HashOK

end VG.Proof.Pbkdf2.Md.Arm
