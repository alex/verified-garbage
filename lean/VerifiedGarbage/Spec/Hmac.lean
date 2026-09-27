import VerifiedGarbage.Spec.Sha256

/-!
# HMAC (RFC 2104; FIPS 198-1)

**Trusted** (as every file in `Spec/`). The keyed-hash message
authentication code HMAC, over any hash function with an input block size,
transcribed from FIPS 198-1, *The Keyed-Hash Message Authentication Code*
(July 2008), §4 (the same construction as RFC 2104 §2). Keys, messages and
digests are sequences of bytes.

Its contracts on each target, for HMAC-SHA-256, are in `Spec/Hmac/<Target>.lean`.
-/

namespace VG.Spec.Hmac

/-- A hash function, as HMAC uses it: its input block size `B` in bytes, and
the digest of a message. -/
structure HashFunction where
  blockSize : Nat
  hash : List Byte → List Byte

/-- `ipad` and `opad` (FIPS 198-1 §3): the bytes `0x36` and `0x5c`, repeated `B` times. -/
def ipad : Byte := 0x36
def opad : Byte := 0x5c

/-- `k ⊕ (pad repeated)`. -/
def xorPad (k : List Byte) (pad : Byte) : List Byte := k.map (· ^^^ pad)

variable (H : HashFunction)

/-- Steps 1–3: the key `K₀`, of exactly `B` bytes. A key of `B` bytes is used
as is; a longer key is hashed first; either is then padded with zeros to
`B` bytes. -/
def blockKey (key : List Byte) : List Byte :=
  let k := if H.blockSize < key.length then H.hash key else key
  k ++ List.replicate (H.blockSize - k.length) 0

/-- Steps 4–9, from `K₀`: `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`. -/
def hmacBlockKey (k0 text : List Byte) : List Byte :=
  H.hash (xorPad k0 opad ++ H.hash (xorPad k0 ipad ++ text))

/-- `HMAC(K, text)`. -/
def hmac (key text : List Byte) : List Byte := hmacBlockKey H (blockKey H key) text

/-- SHA-256 (block size 64 bytes, FIPS 180-4 §1). -/
def sha256 : HashFunction := ⟨64, Sha256.hash⟩

end VG.Spec.Hmac
