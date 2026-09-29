import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM-1024: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of ML-KEM-1024's key
generation, encapsulation key check, encapsulation and decapsulation, and of
the compression of polynomials to the widths only ML-KEM-1024 uses, in terms
of `Spec/MlKem.lean`, for any target: `A` is the target's calling convention.

They are those of ML-KEM-768 (`Spec/MlKem/Contract.lean`, whose notes all
apply here) for the parameter set `mlKem1024` (FIPS 203 Table 2: `k = 4`,
`η₁ = η₂ = 2`, `d_u = 11`, `d_v = 5`), with its sizes (Table 3): an
encapsulation key of 1568 bytes, a decapsulation key of 3168 bytes, and a
ciphertext of 1568 bytes. The same outcome (`Outcome`: 1, or 0 only if some
`SampleNTT` does not finish within `minIterations` iterations), the same leak
(`ρ`, the seed of `Â`, public in the encapsulation key, and nothing else: in
particular, not whether decapsulation rejected the ciphertext implicitly),
and the same keys: a decapsulation key is kept as the seed `d ‖ z` and
expanded by `vg_mlkem1024_keygen`, so there is no decapsulation key check.

The working space `scratch` is 48 KiB, for the 16 entries of `Â` (the
matrix is 4 × 4) besides what ML-KEM-768 needs.

The polynomial primitives of `Spec/MlKem/Poly.lean` serve every parameter
set but for compression: `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` take the widths of ML-KEM-768 (1, 4 and 10), and
ML-KEM-1024 compresses to 11 (`d_u`) and 5 (`d_v`), which
`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress` take.
(They have a name of their own, not `vg_mlkem_compress_encode_…`: a
function named after another with a suffix and the same signature is a
variant of it to `ci/check_variants.py`.)
-/

namespace VG.Spec.MlKem1024

open Spec.MlKem
open Sha3 (bytesAt)

/-! ## Compression to 5 and 11 bits -/

/-- The values of `d` that ML-KEM-1024 compresses to, but ML-KEM-768 does
not (`d_v` and `d_u`, Table 2). -/
def compressWidths : List Nat := [5, 11]

/-- `vg_mlkem1024_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize)`. -/
def compressEncodeSig : Sig where
  params := [("f", .array false .u32 256), ("d", .int .u32 true), ("out", .slice true .u8 "len")]

/-- If `d` is in `compressWidths`, `len = 32d` and the polynomial at `f` is
reduced: writes `ByteEncode_d(Compress_d(f))` to `out`. -/
def compressEncodeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressEncodeSig.contract A
    (pre := fun f d _out len m =>
      d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat ∧ Reduced m f)
    (post := fun f d out len m m' _ =>
      bytesAt m' out len.toNat = compressEncode d.toNat (polyAt m f))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem1024_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256])`. -/
def decodeDecompressSig : Sig where
  params := [("b", .slice false .u8 "len"), ("d", .int .u32 true), ("f", .array true .u32 256)]

/-- If `d` is in `compressWidths` and `len = 32d`: writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`,
reduced. -/
def decodeDecompressContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decodeDecompressSig.contract A
    (pre := fun _b len d _f _m => d.toNat ∈ compressWidths ∧ len.toNat = 32 * d.toNat)
    (post := fun b len d f m m' _ =>
      PolyIs m' f (decodeDecompress d.toNat (bytesAt m b len.toNat)))
    (writeArgs := true)
    (stack := stack)

/-! ## Key generation, the key check, encapsulation and decapsulation -/

/-- `vg_mlkem1024_keygen(seed: *const [u8; 64], ek: *mut [u8; 1568], dk: *mut [u8; 3168], scratch: *mut [u64; 6144]) -> u32`.
`seed` holds `d ‖ z`; `scratch` is working space. -/
def keyGenSig : Sig where
  params := [("seed", .array false .u8 64), ("ek", .array true .u8 1568),
    ("dk", .array true .u8 3168), ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the 64 bytes `d ‖ z` at `seed`: writes
`ML-KEM.KeyGen_internal(d, z)` (Algorithm 16) of ML-KEM-1024 to `ek` and
`dk`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed
of `Â` in the encapsulation key. -/
def keyGenContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => keyGenInternal mlKem1024 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1568, bytesAt m' dk 3168))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m => leakRho (keyGenRho mlKem1024 (bytesAt m seed 32)))

/-- `vg_mlkem1024_check_ek(ek: *const [u8; 1568]) -> u32`. -/
def checkEkSig : Sig where
  params := [("ek", .array false .u8 1568)]
  ret := some .u32

/-- Returns 1 if the 1568 bytes at `ek` pass the encapsulation key check of
§7.2 for ML-KEM-1024 (the modulus check: every integer they encode is less
than `q`), and 0 otherwise. Constant time. -/
def checkEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkEkSig.contract A
    (post := fun ek m _m' r => r = if ekCheck mlKem1024 (bytesAt m ek 1568) then 1 else 0)
    (stack := stack)

/-- `vg_mlkem1024_encaps(ek: *const [u8; 1568], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1568], scratch: *mut [u64; 6144]) -> u32`.
`m` is the randomness; `scratch` is working space. -/
def encapsSig : Sig where
  params := [("ek", .array false .u8 1568), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 1568),
    ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the encapsulation key at `ek` and the 32 bytes of randomness at
`m`: writes the shared secret key and the ciphertext of
`ML-KEM.Encaps_internal(ek, m)` (Algorithm 17) of ML-KEM-1024 to `key` and
`ct`, and returns 1; or returns 0 (see `Outcome`). May leak `ρ`, the seed of
`Â` in `ek`. (The contract holds for any `ek`; the standard requires it to
have passed the check of §7.2.) -/
def encapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => encapsInternal mlKem1024 iters (bytesAt m ek 1568) (bytesAt m msg 32))
        r (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m => leakRho (ekRho mlKem1024 (bytesAt m ek 1568)))

/-- `vg_mlkem1024_decaps(dk: *const [u8; 3168], ct: *const [u8; 1568], key: *mut [u8; 32], scratch: *mut [u64; 6144]) -> u32`.
`scratch` is working space. -/
def decapsSig : Sig where
  params := [("dk", .array false .u8 3168), ("ct", .array false .u8 1568),
    ("key", .array true .u8 32), ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- With the decapsulation key at `dk` and the ciphertext at `ct`: writes
the shared secret key `ML-KEM.Decaps_internal(dk, c)` (Algorithm 18) of
ML-KEM-1024 to `key`, and returns 1; or returns 0 (see `Outcome`). May leak
`ρ`, the seed of `Â` in the encapsulation key in `dk`, and nothing else: in
particular, not whether the ciphertext was rejected implicitly. -/
def decapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => decapsInternal mlKem1024 iters (bytesAt m dk 3168) (bytesAt m ct 1568))
        r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m => leakRho (dkRho mlKem1024 (bytesAt m dk 3168)))

/-! ## The functions on every target -/

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

/-- `vg_mlkem1024_compress_encode` on every target. -/
def compressEncodeApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_compress_encode"
  sig := compressEncodeSig
  writeArgs := true
  summary := "`ByteEncode_d(Compress_d(f))` (FIPS 203 (4.7) and Algorithm 5) for the widths of \
    ML-KEM-1024: writes the 256 coefficients of `*f` (each less than `q` = 3329), compressed to \
    `d` bits, to `out` as `d`-bit little-endian fields.\n\n\
    Contract: `VG.Spec.MlKem1024.compressEncodeContract`. Constant time: only the pointers, `d` \
    and `len` may affect timing, not the data."
  safety := ["`d` must be 5 or 11, and `len` must be `32 * d`.",
    "Each of the 256 `u32`s of `f` must be less than 3329."]

/-- `vg_mlkem1024_decode_decompress` on every target. -/
def decodeDecompressApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_decode_decompress"
  sig := decodeDecompressSig
  writeArgs := true
  summary := "`Decompress_d(ByteDecode_d(b))` (FIPS 203 Algorithm 6 and (4.8)) for the widths of \
    ML-KEM-1024: writes the 256 `d`-bit little-endian fields of the `len` bytes at `b`, \
    decompressed, to `*f` (each less than `q` = 3329).\n\n\
    Contract: `VG.Spec.MlKem1024.decodeDecompressContract`. Constant time: only the pointers, \
    `d` and `len` may affect timing, not the data."
  safety := ["`d` must be 5 or 11, and `len` must be `32 * d`."]

/-- `vg_mlkem1024_keygen` on every target. -/
def keyGenApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_keygen"
  sig := keyGenSig
  writeArgs := true
  summary := "ML-KEM-1024 key generation from a seed, `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 \
    Algorithm 16): with `d` in bytes 0–31 of `*seed` and `z` in bytes 32–63, writes the \
    encapsulation key to `*ek` and the decapsulation key to `*dk`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem1024.keyGenContract`. Constant time but for `ρ`: timing may depend \
    on the pointers and on `ρ` (the last 32 bytes of the encapsulation key), but not on \
    anything else of the seed or the keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 203 §3.3), or a seed so generated \
      before.",
    scratchSafety]

/-- `vg_mlkem1024_check_ek` on every target. -/
def checkEkApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_check_ek"
  sig := checkEkSig
  summary := "The ML-KEM-1024 encapsulation key check (FIPS 203 §7.2): returns 1 if every \
    12-bit integer that the first 1536 bytes of `*ek` encode is less than `q` = 3329 (the \
    modulus check), and 0 otherwise. An encapsulation key must pass it before it is given to \
    `vg_mlkem1024_encaps`.\n\n\
    Contract: `VG.Spec.MlKem1024.checkEkContract`. Constant time: only the pointer may affect \
    timing."
  safety := []

/-- `vg_mlkem1024_encaps` on every target. -/
def encapsApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_encaps"
  sig := encapsSig
  writeArgs := true
  summary := "ML-KEM-1024 encapsulation with given randomness, `ML-KEM.Encaps_internal(ek, m)` \
    (FIPS 203 Algorithm 17): with the encapsulation key `*ek` and the randomness `*m`, writes \
    the shared secret key to `*key` and the ciphertext to `*ct`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem1024.encapsContract`. Constant time but for `ρ`: timing may depend \
    on the pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the \
    key, on the randomness or on the outputs."
  safety := [
    "`ek` must have passed `vg_mlkem1024_check_ek` (FIPS 203 §7.2).",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafety]

/-- `vg_mlkem1024_decaps` on every target. -/
def decapsApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_decaps"
  sig := decapsSig
  writeArgs := true
  summary := "ML-KEM-1024 decapsulation, `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm \
    18): with the decapsulation key `*dk` and the ciphertext `*ct`, writes the shared secret key \
    to `*key`, which is the implicit rejection key `J(z ‖ c)` if the ciphertext does not \
    re-encrypt to itself. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem1024.decapsContract`. Constant time but for `ρ`: timing may depend \
    on the pointers and on `ρ` (bytes 3072–3103 of `*dk`), but not on anything else of the key, \
    on the ciphertext, or on whether it was rejected."
  safety := [
    "`dk` must have been written by `vg_mlkem1024_keygen` (so that it passes the checks of \
      FIPS 203 §7.3).",
    scratchSafety]

end VG.Spec.MlKem1024
