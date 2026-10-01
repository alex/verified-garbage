import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.TCB.Artifact

/-!
# ML-KEM-768: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of ML-KEM-768's
key generation, encapsulation key check, encapsulation and decapsulation,
in terms of `Spec/MlKem.lean`, for any target: `A` is the target's calling
convention. The signatures fix where the arguments are, the memory each
function may access, disjointness, and that the pointers are public (see
`TCB/Sig.lean`); the contracts add the postconditions and what the functions
may leak.

The functions are the internal algorithms of §6, on randomness that the
caller generates (§7.1, §7.2: `ML-KEM.KeyGen` and `ML-KEM.Encaps` are these
on fresh random bytes from an approved RBG), and the input check of §7.2.
A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
from (§3.3): `vg_mlkem768_keygen` expands it into the encapsulation key and
the decapsulation key, which is only ever passed to `vg_mlkem768_decaps`.
So the decapsulation keys it is given pass the checks of §7.3 by
construction, and there is no function for them. An encapsulation key from
elsewhere must pass `vg_mlkem768_check_ek` before it is used (§7.2).

An implementation may bound `SampleNTT`'s loop, as Appendix B allows, by
`minIterations` iterations or more. So every function that samples returns
1 with the output of the (unbounded) algorithm of the standard, or 0, only
if some `SampleNTT` does not finish within `minIterations` iterations
(which happens with probability less than 2⁻²⁶¹ per `SampleNTT`, Table 4):
its outputs are then unspecified, and the caller must destroy them with the
other intermediate values and treat the operation as failed (Appendix B).
See `Outcome`.

Everything is secret but `ρ`, the seed of the matrix `Â`, which is part of
the encapsulation key and so public: `SampleNTT`'s loop takes a number of
iterations that depends on it. The functions may leak it (`Sig.contract`'s
`leak`), and nothing else: in particular, not whether decapsulation
rejected the ciphertext implicitly (§6.3). The working space `scratch`
holds intermediate values on return, which the caller must destroy (§3.3).
It is 32 KiB: room for 28 polynomials of 32-bit coefficients (1 KiB each),
the state of a Keccak computation and its working space.

The functions may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`), to pass arguments to the
functions they call, and take the number of bytes of stack below the stack
pointer that their calls and frames use (`stack`, see `Sig.contract`),
which depends on the target.
-/

namespace VG.Spec.MlKem

open Sha3 (bytesAt)

/-- The return value `r` of a function that computes, with `SampleNTT`
bounded, an algorithm `f iters` (bounding each `SampleNTT` by `iters`
iterations), and outputs `out`: either 1, with `out` the output of the
algorithm of the standard (the output of `f iters` for some bound), or 0,
if `SampleNTT` does not finish within `minIterations` iterations. -/
def Outcome {α : Type} (f : Nat → Option α) (r : BitVec 32) (out : α) : Prop :=
  (r = 1 ∧ ∃ iters, f iters = some out) ∨ (r = 0 ∧ f minIterations = none)

/-- The bytes of `ρ`, as the numbers a contract declares that a function may
leak. -/
def leakRho (ρ : List Byte) : List Nat := ρ.map (·.toNat)

/-- `vg_mlkem768_keygen(seed: *const [u8; 64], ek: *mut [u8; 1184], dk: *mut [u8; 2400], scratch: *mut [u64; 4096]) -> u32`.
`seed` holds `d ‖ z`; `scratch` is working space. -/
def keyGenSig : Sig where
  params := [("seed", .array false .u8 64), ("ek", .array true .u8 1184),
    ("dk", .array true .u8 2400), ("scratch", .array true .u64 4096)]
  ret := some .u32

/-- With the 64 bytes `d ‖ z` at `seed`: writes
`ML-KEM.KeyGen_internal(d, z)` (Algorithm 16) of ML-KEM-768 to `ek` and
`dk`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed
of `Â` in the encapsulation key. -/
def keyGenContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => keyGenInternal mlKem768 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1184, bytesAt m' dk 2400))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m => leakRho (keyGenRho mlKem768 (bytesAt m seed 32)))

/-- `vg_mlkem768_check_ek(ek: *const [u8; 1184]) -> u32`. -/
def checkEkSig : Sig where
  params := [("ek", .array false .u8 1184)]
  ret := some .u32

/-- Returns 1 if the 1184 bytes at `ek` pass the encapsulation key check of
§7.2 for ML-KEM-768 (the modulus check: every integer they encode is less
than `q`), and 0 otherwise. Constant time. -/
def checkEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkEkSig.contract A
    (post := fun ek m _m' r => r = if ekCheck mlKem768 (bytesAt m ek 1184) then 1 else 0)
    (stack := stack)

/-- `vg_mlkem768_encaps(ek: *const [u8; 1184], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1088], scratch: *mut [u64; 4096]) -> u32`.
`m` is the randomness; `scratch` is working space. -/
def encapsSig : Sig where
  params := [("ek", .array false .u8 1184), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 1088),
    ("scratch", .array true .u64 4096)]
  ret := some .u32

/-- With the encapsulation key at `ek` and the 32 bytes of randomness at
`m`: writes the shared secret key and the ciphertext of
`ML-KEM.Encaps_internal(ek, m)` (Algorithm 17) of ML-KEM-768 to `key` and
`ct`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed of
`Â` in `ek`. (The contract holds for any `ek`; the standard requires it to
have passed the check of §7.2.) -/
def encapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => encapsInternal mlKem768 iters (bytesAt m ek 1184) (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m => leakRho (ekRho mlKem768 (bytesAt m ek 1184)))

/-- `vg_mlkem768_decaps(dk: *const [u8; 2400], ct: *const [u8; 1088], key: *mut [u8; 32], scratch: *mut [u64; 4096]) -> u32`.
`scratch` is working space. -/
def decapsSig : Sig where
  params := [("dk", .array false .u8 2400), ("ct", .array false .u8 1088),
    ("key", .array true .u8 32), ("scratch", .array true .u64 4096)]
  ret := some .u32

/-- With the decapsulation key at `dk` and the ciphertext at `ct`: writes
the shared secret key `ML-KEM.Decaps_internal(dk, c)` (Algorithm 18) of
ML-KEM-768 to `key`, and returns 1; or returns 0 (see `Outcome`). May leak
`ρ`, the seed of `Â` in the encapsulation key in `dk`, and nothing else: in
particular, not whether the ciphertext was rejected implicitly. -/
def decapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => decapsInternal mlKem768 iters (bytesAt m dk 2400) (bytesAt m ct 1088))
        r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m => leakRho (dkRho mlKem768 (bytesAt m dk 2400)))

/-- What the documentation says of the return value of a function whose
`SampleNTT` is bounded. -/
private def outcomeDoc : String :=
  "Returns 1 on success. Returns 0 if a `SampleNTT` (FIPS 203 Algorithm 7) reaches the bound \
    on its loop's iterations, which is at least 280 (FIPS 203 Appendix B; this happens with \
    probability less than 2^-261): the outputs are then unspecified, and the caller must \
    destroy them and treat the operation as failed."

/-- What the documentation says of the working space. -/
private def scratchSafety : String :=
  "`scratch` is working space: on return it holds intermediate values, which the caller must \
    destroy (FIPS 203 §3.3)."

/-- `vg_mlkem768_keygen` on every target. -/
def keyGenApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_keygen"
  sig := keyGenSig
  writeArgs := true
  contracts := some fun A stack => keyGenContract A stack
  summary := "ML-KEM-768 key generation from a seed, `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 \
    Algorithm 16): with `d` in bytes 0–31 of `*seed` and `z` in bytes 32–63, writes the \
    encapsulation key to `*ek` and the decapsulation key to `*dk`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem.keyGenContract`. Constant time but for `ρ`: timing may depend on \
    the pointers and on `ρ` (the last 32 bytes of the encapsulation key), but not on anything \
    else of the seed or the keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 203 §3.3), or a seed so generated \
      before.",
    scratchSafety]

/-- `vg_mlkem768_check_ek` on every target. -/
def checkEkApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_check_ek"
  sig := checkEkSig
  contracts := some fun A stack => checkEkContract A stack
  summary := "The ML-KEM-768 encapsulation key check (FIPS 203 §7.2): returns 1 if every 12-bit \
    integer that the first 1152 bytes of `*ek` encode is less than `q` = 3329 (the modulus \
    check), and 0 otherwise. An encapsulation key must pass it before it is given to \
    `vg_mlkem768_encaps`.\n\n\
    Contract: `VG.Spec.MlKem.checkEkContract`. Constant time: only the pointer may affect \
    timing."
  safety := []

/-- `vg_mlkem768_encaps` on every target. -/
def encapsApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_encaps"
  sig := encapsSig
  writeArgs := true
  contracts := some fun A stack => encapsContract A stack
  summary := "ML-KEM-768 encapsulation with given randomness, `ML-KEM.Encaps_internal(ek, m)` \
    (FIPS 203 Algorithm 17): with the encapsulation key `*ek` and the randomness `*m`, writes \
    the shared secret key to `*key` and the ciphertext to `*ct`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem.encapsContract`. Constant time but for `ρ`: timing may depend on \
    the pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the key, \
    on the randomness or on the outputs."
  safety := [
    "`ek` must have passed `vg_mlkem768_check_ek` (FIPS 203 §7.2).",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafety]

/-- `vg_mlkem768_decaps` on every target. -/
def decapsApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_decaps"
  sig := decapsSig
  writeArgs := true
  contracts := some fun A stack => decapsContract A stack
  summary := "ML-KEM-768 decapsulation, `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm \
    18): with the decapsulation key `*dk` and the ciphertext `*ct`, writes the shared secret key \
    to `*key`, which is the implicit rejection key `J(z ‖ c)` if the ciphertext does not \
    re-encrypt to itself. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem.decapsContract`. Constant time but for `ρ`: timing may depend on \
    the pointers and on `ρ` (bytes 2304–2335 of `*dk`), but not on anything else of the key, on \
    the ciphertext, or on whether it was rejected."
  safety := [
    "`dk` must have been written by `vg_mlkem768_keygen` (so that it passes the checks of \
      FIPS 203 §7.3).",
    scratchSafety]

end VG.Spec.MlKem
