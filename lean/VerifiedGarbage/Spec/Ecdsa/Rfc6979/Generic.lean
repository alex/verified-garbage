import VerifiedGarbage.Spec.Ecdsa.Rfc6979
import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Deterministic ECDSA over any curve and hash: the contracts, on every target

**Trusted** (as every file in `Spec/`). An `Instance` is a curve's
`Ecdsa.Instance`, a hash function for HMAC, its names, its output length
and the bound on candidates: `vg_ecdsa_<curve>_<hash>_sign`, in the module
`ecdsa_<curve>_<hash>`, signs as RFC 6979 does (`Rfc6979.sign`).

It takes the private key `d` (`len` octets, most significant first) and the
hash `digest` (`hashLen` octets, the hash function's output), and returns 1
and writes the signature (`encode`), or returns 0 and writes zeros if `d`
is not in `[1, n-1]` or none of the first `tries` candidates is suitable.

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`; the contents of every buffer are secret.
The number of candidates tried may affect timing (`leak`): an implementation
may stop at the first suitable one. It is 0 for an invalid key and almost
always 1 otherwise; the key and the hash may not affect timing in any other
way. `scratch` is 8 KiB of working space, whose contents on return are
unspecified. `stack` is the number of bytes below the stack pointer that an
implementation's calls and frames use. The function may overwrite its
arguments passed in memory, where the calling convention allows it
(`writeArgs`).
-/

namespace VG.Spec.Ecdsa.Rfc6979

open Weierstrass

/-- A curve, a hash function for HMAC, and their names in the Rust
interface. -/
structure Instance where
  ecdsa : Ecdsa.Instance
  hash : Hmac.HashFunction
  /-- The length of the hash function's output, in octets. -/
  hashLen : Nat
  /-- The name in function and module names, e.g. `sha256`. -/
  hashName : String
  /-- The name in documentation, e.g. `SHA-256`. -/
  hashTitle : String
  /-- The most candidates `sign` tries. -/
  tries : Nat

namespace Instance

variable (I : Instance)

/-- `(out: *mut [u8; 2 len], d: *const [u8; len], digest: *const [u8; hashLen],
scratch: *mut [u64; 1024]) -> u32`. -/
def signSig : Sig where
  params := [("out", .array true .u8 (2 * I.ecdsa.curve.len)),
    ("d", .array false .u8 I.ecdsa.curve.len), ("digest", .array false .u8 I.hashLen),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- RFC 6979's signature of `digest` with the private key `d`, and the
number of candidates tried. -/
def result (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  sign I.ecdsa.curve I.hash I.hashLen I.tries (ofBytes (bytesAt m d I.ecdsa.curve.len))
    (bytesAt m digest I.hashLen)

/-- The deterministic signature of `digest` with the private key `d`, if
there is one (`Rfc6979.sign`): then the function returns 1 and writes it
(`encode`) to `out`; otherwise it returns 0 and writes zeros to `out`.
Constant time but for the number of candidates tried. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.signSig.contract A
    (post := fun out d digest _scratch m m' r =>
      match (I.result m d digest).1 with
      | some rs => r = 1 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
      | none => r = 0 ∧ bytesAt m' out (2 * I.ecdsa.curve.len) =
          List.replicate (2 * I.ecdsa.curve.len) 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out d digest _scratch m => [(I.result m d digest).2])

/-- `vg_ecdsa_<curve>_<hash>_sign` on every target. -/
def signApi : Api where
  module := s!"ecdsa_{I.ecdsa.name}_{I.hashName}"
  name := s!"vg_ecdsa_{I.ecdsa.name}_{I.hashName}_sign"
  sig := I.signSig
  writeArgs := true
  contracts := some fun A stack => I.signContract A stack
  summary := s!"Deterministic ECDSA signature generation over {I.ecdsa.title} with \
    HMAC-{I.hashTitle} (RFC 6979 §3.2; FIPS 186-5 §6.4.1): with the private key `d` \
    ({I.ecdsa.curve.len} bytes, most significant first), signs the {I.hashTitle} hash at \
    `digest` ({I.hashLen} bytes), deriving the per-message secret number `k` from the key \
    and the hash. Returns 1 and writes `r` then `s` ({I.ecdsa.curve.len} bytes each, most \
    significant first) to `*out`; or returns 0 and writes zeros to `*out` if `d` is not in \
    `[1, n-1]`, or if none of the first {I.tries} candidates for `k` is suitable (which \
    does not happen in practice).\n\n\
    Contract: `VG.Spec.Ecdsa.Rfc6979.Instance.signContract`. Constant time but for the \
    number of candidates for `k` tried (almost always 1): timing may depend on the \
    pointers and that number, not otherwise on the key or the hash."
  safety := ["The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

end Instance

end VG.Spec.Ecdsa.Rfc6979
