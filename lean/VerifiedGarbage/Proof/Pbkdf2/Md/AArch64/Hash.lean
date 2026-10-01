import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the hash function

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Md/X86_64/Hash.lean`), `HashOK H` is what the proofs know of
the hash function whose code `H` describes: it is a Merkle–Damgård hash
function `md` (`Md`) whose length field and digest code do what they should
(`Shape`), with a verified compression function (`CompOk`); its streaming
functions are verified against the contracts HMAC's generic proofs call
them with (`stream`); its specification is `md` from the initial hash value
`iv`, with the digest the first `D` bytes of `md`'s; and its sizes fit.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64 VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (Shape CompOk Sizes)
open VG.Proof.Hmac.Generic.Common (bytesAt_reloc)
open Spec.Hmac (StreamingHash)

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs of `iterate` see it. -/
  md : Md H.P.B H.P.N H.P.L
  shape : Shape md
  /-- The compression function is verified. -/
  comp : CompOk md H.P.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The length field is right for every message shorter than 2⁶⁴ bytes. -/
  lenOk : ∀ n, n < 2 ^ 64 → md.lenOk n
  /-- The streaming functions, verified. -/
  stream : Hmac.Generic.AArch64.HashOK H.stream
  /-- Checked no-clobber facts for the MD wrapper call graph. -/
  initKeepsV : H.initC.allInstrs keepsV = true
  updKeepsV : H.updC.allInstrs keepsV = true
  finKeepsV : H.finC.allInstrs keepsV = true
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m ↔ md.Repr iv mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  /-- The sizes. -/
  sizes : Sizes H.P H.D H.W
  L : 0 < H.P.L ∧ H.P.L ≤ 16
  W : H.W ≤ 256

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.P.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.P.N + H.P.B := hH.stream.hS
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.P.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B_pos : 0 < H.P.B := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem N_le : H.P.N ≤ 64 := hH.sizes.dims.N.2

/-- What the proof of `iterate` (`Proof/Pbkdf2/AArch64/Iterate.lean`) needs
of the hash function. -/
theorem iterOk : Pbkdf2.AArch64.HashOk H.P H.D H.W hH.SH hH.md hH.iv where
  sizes := hH.sizes
  shape := hH.shape
  reloc := hH.reloc
  lenOk := hH.lenOk _ (by have := hH.B_le; have := hH.sizes.DN; have := hH.N_le; omega)
  link := ⟨hH.hB, hH.hS, hH.hD, fun m p x h => (hH.repr m p x).1 h, hH.hash, hH.sizes.DN,
    by have := hH.sizes.pad; have := hH.sizes.NL; omega⟩

include hH in
/-- The MD PBKDF2 wrapper uses only scalar instructions around its certified callees. -/
theorem pbkdf2_keepsV : H.pbkdf2.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hu := hH.updKeepsV
  have hf := hH.finKeepsV
  have ht : H.iterate.allInstrs keepsV = true :=
    Pbkdf2.AArch64.iterate_keepsV hH.shape hH.comp.keepsV
  have hinit : H.hmacInit.allInstrs keepsV = true := by
    simp [Hash.hmacInit, Hash.stream, Impl.Hmac.Generic.AArch64.Hash.init,
      Impl.Hmac.Generic.AArch64.Hash.initKeys, Impl.Hmac.Generic.AArch64.Hash.initPrologue,
      Impl.Hmac.Generic.AArch64.Hash.keyLoop, Impl.Hmac.Generic.AArch64.Hash.padLoop,
      Impl.Hmac.Generic.AArch64.Hash.callInit, Impl.Hmac.Generic.AArch64.Hash.callUpd,
      Impl.Hmac.Generic.AArch64.Hash.save, Impl.Hmac.Generic.AArch64.Hash.saved,
      Impl.Hmac.Generic.AArch64.Hash.restore, Impl.Hmac.Generic.AArch64.left,
      Impl.Sha256.AArch64.Stream.mov, Code.allInstrs, keepsV, vdstOf, hi, hu]
  have hfin : H.hmacFin.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hf ⊢
    simp [Hash.hmacFin, Hash.finMid, Hash.finOut, Hash.copy32, Hash.stream,
      Impl.Hmac.Generic.AArch64.Hash.finPrologue, Impl.Hmac.Generic.AArch64.Hash.callFin,
      Impl.Hmac.Generic.AArch64.Hash.save, Impl.Hmac.Generic.AArch64.Hash.saved,
      Impl.Hmac.Generic.AArch64.Hash.restore, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, Impl.Sha256.AArch64.Stream.mov, instrs, keepsV, vdstOf, hf]
  have hk : H.key.allInstrs keepsV = true := by
    simp [Hash.key, Hash.keyShr, Hash.keySub, Hash.short, Hash.hashKey, Hash.hkInit,
      Hash.hkUpd, Hash.hkFin, Hash.hkKey, Impl.MdStream.AArch64.mov,
      Code.allInstrs, keepsV, vdstOf, hi, hu, hf]
  have hs : H.setup.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hinit hu ⊢
    simp [Hash.setup, Hash.initArgs, Hash.saltArgs, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hinit, hu]
  have hb : H.block.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hu hfin ht ⊢
    simp [Hash.block, Hash.intArgs, Hash.finArgs, Hash.iterArgs, Hash.outLen,
      Hash.outLoop, Hash.advance, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hu, hfin, ht]
  simp [Hash.pbkdf2, Hash.entry, Hash.entryPre, Hash.entryPost, Hash.loopRegs,
    Hash.exit, Impl.Hmac.Generic.AArch64.Hash.save, Impl.Hmac.Generic.AArch64.Hash.saved,
    Impl.Hmac.Generic.AArch64.Hash.restore, Impl.MdStream.AArch64.mov,
    Code.allInstrs, keepsV, vdstOf, hk, hs, hb]

end HashOK

end VG.Proof.Pbkdf2.Md.AArch64
