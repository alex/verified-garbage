import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2-HMAC-SHA-256: one step as two compressions

Untrusted: everything here is checked by Lean. For a 64-byte key `K₀`, both
hashes of HMAC-SHA-256 of a 32-byte `U` are of 96-byte messages: a block
(`K₀ ⊕ ipad` or `K₀ ⊕ opad`) whose compression is the state
`vg_hmac_sha256_init` leaves, then 32 bytes, which the padding completes to
a second block (`block96`). So a step of PBKDF2's iteration is two
compressions, whatever the target.
-/

namespace VG.Proof.Pbkdf2

open VG.Spec.Sha256 (HashValue Block compress compressList parseBlock wordBytes H0)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open VG.Proof.Sha256.Stream (lenBytes hash_one compressList_append)

/-- The padding of a 96-byte message after its first 64 + 32 bytes: `0x80`,
zeros, and the length in bits (768), big-endian. -/
def pad96 : List Byte := [0x80] ++ List.replicate 23 0 ++ [0, 0, 0, 0, 0, 0, 3, 0]

/-- The last block of a 96-byte message whose last 32 bytes are `x`. -/
def block96 (x : List Byte) : Block := parseBlock fun t => (x ++ pad96).getD t 0

/-- A hash value as 32 big-endian bytes. -/
def digest (H : HashValue) : List Byte := H.toList.flatMap wordBytes

theorem digest_length (H : HashValue) : (digest H).length = 32 := by
  simp [digest, wordBytes, List.length_flatMap, List.map_const']

theorem lenBytes96 {m : List Byte} (h : m.length = 96) : lenBytes m = [0, 0, 0, 0, 0, 0, 3, 0] := by
  simp only [lenBytes, h]; decide

/-- SHA-256 of a 96-byte message. -/
theorem hash96 {p x : List Byte} (hp : p.length = 64) (hx : x.length = 32) :
    Spec.Sha256.hash (p ++ x) = digest (compress (compressList H0 p 1) (block96 x)) := by
  have hl : (p ++ x).length = 96 := by simp [hp, hx]
  rw [hash_one (by omega), hl]
  simp only [digest, block96, pad96]
  have e₁ : compressList H0 (p ++ x) (96 / 64) = compressList H0 p 1 := by
    rw [show 96 / 64 = 1 by rfl, compressList_append (by omega)]
  have e₂ : Sha256.Stream.rest (p ++ x) = x := by
    simp only [Sha256.Stream.rest, hl]
    rw [show 64 * (96 / 64) = p.length by omega, List.drop_left]
  rw [e₁, e₂, lenBytes96 hl, show 55 - 96 % 64 = 23 by rfl]
  simp only [List.append_assoc]

/-- One step of the iteration: HMAC-SHA-256 of a 32-byte message, from the
hash values of the key's two blocks. -/
theorem hmac_step {k0 u : List Byte} (hk : k0.length = 64) (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u =
      digest (compress (compressList H0 (xorPad k0 opad) 1)
        (block96 (digest (compress (compressList H0 (xorPad k0 ipad) 1) (block96 u))))) := by
  have hi : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have ho : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  simp only [hmacBlockKey, sha256]
  rw [hash96 hi hu, hash96 ho (digest_length _)]

end VG.Proof.Pbkdf2
