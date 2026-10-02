import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.TCB.Artifact

/-!
# ECDSA over any curve: the contracts, on every target

**Trusted** (as every file in `Spec/`). An `Instance` is a curve as the Rust
interface has it: the curve, its name in the functions' names
(`vg_ecdsa_<name>_sign`, in the module `ecdsa_<name>`), and its name in
their documentation. Each curve is an `Instance` in a file of its own
(`Spec/Ecdsa/P256.lean`, …), and needs nothing else.

`sign` takes the private key `d`, the hash and the per-message secret
number `k`, each as `len` octets, most significant first. The hash is
`len` octets too: its leftmost `len` octets if it is longer, and padded on
the left with zeros if it is shorter, which leaves its integer value
unchanged. For a curve whose `n` has `8 len` bits (as for every curve with
an `Instance` so far), `hashToInt` of those octets is then FIPS 186-5's `e`.

The signature determines memory validity, separation and that the pointers
are public, through `Sig.contract`; the contents of every buffer are secret.
`sign` returns 1 and writes the signature, or returns 0 and writes zeros:
the return value depends on secrets (though for an honest `k`, it is 0 with
negligible probability). `scratch` is 8 KiB of working space, whose contents
on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

namespace VG.Spec.Ecdsa

open Weierstrass

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s. -/
def scratchWords : Nat := 1024

/-- A curve, and its names in the Rust interface. -/
structure Instance where
  curve : Curve
  /-- The name in function and module names, e.g. `p256`. -/
  name : String
  /-- The name in documentation, e.g. `P-256`. -/
  title : String

namespace Instance

variable (I : Instance)

/-- `(out: *mut [u8; 2 len], d: *const [u8; len], digest: *const [u8; len],
k: *const [u8; len], scratch: *mut [u64; 1024]) -> u32`. -/
def signSig : Sig where
  params := [("out", .array true .u8 (2 * I.curve.len)), ("d", .array false .u8 I.curve.len),
    ("digest", .array false .u8 I.curve.len), ("k", .array false .u8 I.curve.len),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- The signature of `digest` with the private key `d` and the
per-message secret number `k`, if there is one (`signWith`): then the
function returns 1 and writes it (`encode`) to `out`; otherwise it returns 0
and writes zeros to `out`. Constant time: no buffer contents may affect
timing. -/
def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.signSig.contract A
    (post := fun out d digest k _scratch m m' r =>
      match signWith I.curve (ofBytes (bytesAt m d I.curve.len))
          (hashToInt I.curve (bytesAt m digest I.curve.len)) (ofBytes (bytesAt m k I.curve.len)) with
      | some rs => r = 1 ∧ bytesAt m' out (2 * I.curve.len) = encode I.curve rs
      | none => r = 0 ∧ bytesAt m' out (2 * I.curve.len) = List.replicate (2 * I.curve.len) 0)
    (writeArgs := true) (stack := stack)

/-- `vg_ecdsa_<name>_sign` on every target. -/
def signApi : Api where
  module := s!"ecdsa_{I.name}"
  name := s!"vg_ecdsa_{I.name}_sign"
  sig := I.signSig
  writeArgs := true
  contracts := some fun A stack => I.signContract A stack
  summary := s!"ECDSA signature generation over {I.title} (FIPS 186-5 §6.4.1): with the \
    private key `d` and the per-message secret number `k` (each {I.curve.len} bytes, most \
    significant first), signs the hash at `digest`: its leftmost {I.curve.len} bytes, or, \
    for a shorter hash, the hash padded on the left with zeros to {I.curve.len} bytes. \
    Returns 1 and writes `r` then `s` ({I.curve.len} bytes each, most significant first) \
    to `*out`; or returns 0 and writes zeros to `*out` if `d` or `k` is not in `[1, n-1]`, \
    or if `r` or `s` is 0, in which case the caller signs again with another `k`.\n\n\
    Contract: `VG.Spec.Ecdsa.Instance.signContract`. Constant time: only the pointers may \
    affect timing, not the key, the hash or `k`."
  safety := ["`k` must be secret, and never be used to sign two different hashes: it must \
    be chosen uniformly at random in `[1, n-1]` (FIPS 186-5 §A.3) or derived as RFC 6979 \
    does.", "The contents of `scratch` on return are unspecified and may contain secrets; \
    the caller must destroy them after use."]

end Instance

end VG.Spec.Ecdsa
