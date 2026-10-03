import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# ECDSA signature verification over any curve: the contracts, on every target

**Trusted** (as every file in `Spec/`). For a curve's `Ecdsa.Instance`,
`vg_ecdsa_<name>_verify`, in the module `ecdsa_<name>`: whether a signature
of a hash is valid for a public key (`Ecdsa.verify`), with the validation of
the public key.

`verify` takes the public key as `2 len + 1` octets (`04 ‖ x ‖ y`), the hash
as `len` octets as `sign` does (its leftmost `len` octets, or padded on the
left with zeros), and the signature as `2 len` octets (`r` then `s`, as
`sign` writes it). The signature determines memory validity, separation and
that the pointers are public, through `Sig.contract`. Every input is
public: the contents of the three buffers may affect timing (`leak`), so an
implementation may, for instance, reject an invalid key or signature early,
and use variable-time arithmetic. The function returns 1 if the signature
is valid and 0 otherwise. `scratch` is 8 KiB of working space, whose
contents on return are unspecified. `stack` is the number of bytes below the
stack pointer that an implementation's calls and frames use. The function
may overwrite its arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

namespace VG.Spec.Ecdsa

open Weierstrass

namespace Instance

variable (I : Instance)

/-- `(public: *const [u8; 2 len + 1], digest: *const [u8; len],
sig: *const [u8; 2 len], scratch: *mut [u64; 1024]) -> u32`. -/
def verifySig : Sig where
  params := [("public", .array false .u8 (2 * I.curve.len + 1)), ("digest", .array false .u8 I.curve.len),
    ("sig", .array false .u8 (2 * I.curve.len)), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Whether the signature at `sig` of `digest` is valid for the public key
at `public` (`verify`): the function returns 1 if it is and 0 otherwise.
Every input is public, and may affect timing. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  I.verifySig.contract A
    (post := fun pk digest sig _scratch m _m' r =>
      r = if verify I.curve (bytesAt m pk (2 * I.curve.len + 1))
          (hashToInt I.curve (bytesAt m digest I.curve.len)) (bytesAt m sig (2 * I.curve.len))
        then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk digest sig _scratch m =>
      (bytesAt m pk (2 * I.curve.len + 1) ++ bytesAt m digest I.curve.len ++
        bytesAt m sig (2 * I.curve.len)).map (·.toNat))

/-- `vg_ecdsa_<name>_verify` on every target. -/
def verifyApi : Api where
  module := s!"ecdsa_{I.name}"
  name := s!"vg_ecdsa_{I.name}_verify"
  sig := I.verifySig
  writeArgs := true
  contracts := some fun A stack => I.verifyContract A stack
  summary := s!"ECDSA signature verification over {I.title} (FIPS 186-5 §6.4.2): whether \
    the signature at `sig` (`r` then `s`, {I.curve.len} bytes each, most significant first) \
    of the hash at `digest` (its leftmost {I.curve.len} bytes, or, for a shorter hash, the \
    hash padded on the left with zeros to {I.curve.len} bytes) is valid for the public key \
    at `public`, which must be a valid public key in the uncompressed form of SEC 1 \
    §2.3.3 (`04`, then `x` and `y` in {I.curve.len} bytes each, most significant first, \
    both below `p`, on the curve; SP 800-56A §5.6.2.3.3). Returns 1 if it is, and 0 if it \
    is not or the public key is not valid.\n\n\
    Contract: `VG.Spec.Ecdsa.Instance.verifyContract`. Every input is public: timing may \
    depend on the pointers and the contents of `public`, `digest` and `sig`."
  safety := ["The contents of `scratch` on return are unspecified; the caller may reuse or \
    destroy them."]

end Instance

end VG.Spec.Ecdsa
