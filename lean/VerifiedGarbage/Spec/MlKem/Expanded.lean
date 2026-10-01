import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-768 and ML-KEM-1024 with expanded encapsulation keys

**Trusted** (as every file in `Spec/`). Encapsulation samples the matrix
`Â` from the seed `ρ` of the encapsulation key (Algorithm 14, lines 4–8),
and hashes the key (Algorithm 17, line 1: `H(ek)`); decapsulation samples
`Â` again to re-encrypt (Algorithm 18, line 8). Neither depends on anything
but the key, so a caller that keeps a key for more than one operation may
compute them once, when it gets the key, and keep them with it: the
functions below take them as inputs, and their contracts are the same
algorithms of the standard, on the same outputs.

An *expanded encapsulation key* (`ExpandedEk`) is the encapsulation key
`ek`, then `H(ek)` (32 bytes), then `Â` sampled from the `ρ` of `ek`, row by
row, each entry as its 256 coefficients, less than `q`, as little-endian
`u32`s (1 KiB): as the functions of `Spec/MlKem/Poly.lean` take polynomials
(`PolyIs`). For ML-KEM-768 it is 10432 bytes, for ML-KEM-1024 17984.

The functions, for each parameter set:

* `keygen_expanded`: `ML-KEM.KeyGen_internal(d, z)`, as `keygen`, with the
  encapsulation key written expanded;
* `expand_ek`: the expanded key of an encapsulation key from elsewhere, which
  must first pass the check of §7.2;
* `encaps_expanded`: `ML-KEM.Encaps_internal(ek, m)` from the expanded key
  of `ek`;
* `decaps_expanded`: `ML-KEM.Decaps_internal(dk, c)`, with the expanded key
  of the encapsulation key in `dk`.

The two that sample `Â` return 1, or 0 if a `SampleNTT` does not finish
within `minIterations` iterations (`Outcome`), and may leak `ρ`, as the
functions of `Contract.lean` do. The two that take an expanded key sample
nothing: they always succeed, and leak nothing but the pointers.

The same notes apply as in `Contract.lean`: the working space `scratch`
holds intermediate values on return, which the caller must destroy (§3.3),
and the functions may overwrite their arguments passed in memory
(`writeArgs`) and take the stack below the stack pointer that their calls use
(`stack`).
-/

namespace VG.Spec.MlKem

open Sha3 (bytesAt)

/-- The length of an expanded encapsulation key: the key (`384k + 32`
bytes), `H` of it (32 bytes), and the `k²` entries of `Â`, 1 KiB each. -/
def Params.ekxLen (p : Params) : Nat := p.ekLen + 32 + 1024 * (p.k * p.k)

/-- The offset of `Â[i, j]` in an expanded encapsulation key: the entries
follow `H(ek)`, row by row. -/
def Params.ekxA (p : Params) (i j : Nat) : Nat := p.ekLen + 32 + 1024 * (p.k * i + j)

/-- The expanded encapsulation key of `ek` is at `x` in `m`: the bytes of
`ek`, then those of `H(ek)`, then, for some bound on `SampleNTT`'s
iterations for which it samples the matrix `Â` of `K-PKE.Encrypt`
(Algorithm 14, lines 4–8) from the `ρ` of `ek`, each entry `Â[i, j]` at
`ekxA i j`, reduced. -/
def ExpandedEk (p : Params) (m : Mem) (x : Addr) (ek : List Byte) : Prop :=
  bytesAt m x p.ekLen = ek ∧ bytesAt m (x + BitVec.ofNat 64 p.ekLen) 32 = H ek ∧
    ∃ iters A, sampleMatrix p.k iters (ekRho p ek) = some A ∧
      ∀ i < p.k, ∀ j < p.k, PolyIs m (x + BitVec.ofNat 64 (p.ekxA i j)) ((A.getD i []).getD j zero)

/-- The postcondition of `keygen_expanded`, with the seed at `seed`: writes
to `ekx` the expanded key of the encapsulation key of
`ML-KEM.KeyGen_internal(d, z)` (so its first `384k + 32` bytes are the
encapsulation key itself), and the decapsulation key to `dk`, and returns 1;
or returns 0 (see `Outcome`). -/
def KeyGenExpandedPost (p : Params) (seed ekx dk : Addr) (m m' : Mem) (r : BitVec 32) : Prop :=
  Outcome (fun iters => keyGenInternal p iters (bytesAt m seed 32) (bytesAt m (seed + 32) 32)) r
      (bytesAt m' ekx p.ekLen, bytesAt m' dk p.dkLen) ∧
    (r = 1 → ExpandedEk p m' ekx (bytesAt m' ekx p.ekLen))

/-- The postcondition of `expand_ek`: writes to `ekx` the expanded key of
the encapsulation key at `ek` and returns 1, or returns 0 if a `SampleNTT`
of `Â` does not finish within `minIterations` iterations. (It holds for any
`ek`; the standard requires it to have passed the check of §7.2.) -/
def ExpandEkPost (p : Params) (ek ekx : Addr) (m m' : Mem) (r : BitVec 32) : Prop :=
  (r = 1 ∧ ExpandedEk p m' ekx (bytesAt m ek p.ekLen)) ∨
    (r = 0 ∧ sampleMatrix p.k minIterations (ekRho p (bytesAt m ek p.ekLen)) = none)

/-- The postcondition of `encaps_expanded`, given that `ekx` holds the
expanded key of an encapsulation key `ek` (its first `384k + 32` bytes):
writes the shared secret key and the ciphertext of
`ML-KEM.Encaps_internal(ek, m)` (Algorithm 17) to `key` and `ct`. (It holds
for any `ek`; the standard requires it to have passed the check of §7.2.) -/
def EncapsExpandedPost (p : Params) (ekx msg key ct : Addr) (m m' : Mem) : Prop :=
  ∃ iters, encapsInternal p iters (bytesAt m ekx p.ekLen) (bytesAt m msg 32) =
    some (bytesAt m' key 32, bytesAt m' ct p.ctLen)

/-- The precondition of `decaps_expanded`: `ekx` holds the expanded key of
the encapsulation key in the decapsulation key at `dk` (its bytes `384k` to
`768k + 32`). -/
def DecapsExpandedPre (p : Params) (dk ekx : Addr) (m : Mem) : Prop :=
  ExpandedEk p m ekx (bytesAt m (dk + BitVec.ofNat 64 (384 * p.k)) p.ekLen)

/-- The postcondition of `decaps_expanded`: writes the shared secret key
`ML-KEM.Decaps_internal(dk, c)` (Algorithm 18) to `key`. -/
def DecapsExpandedPost (p : Params) (dk ct key : Addr) (m m' : Mem) : Prop :=
  ∃ iters, decapsInternal p iters (bytesAt m dk p.dkLen) (bytesAt m ct p.ctLen) = some (bytesAt m' key 32)

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

/-- What the documentation says of an expanded encapsulation key. -/
private def ekxDoc (p : Params) (name : String) : String :=
  s!"an expanded encapsulation key of {name}: the encapsulation key ({p.ekLen} bytes), then \
    `H(ek)` (32 bytes), then the matrix `Â` sampled from its `ρ` (FIPS 203 Algorithm 14, \
    lines 4–8), row by row, each entry as 256 little-endian `u32` coefficients less than `q` \
    = 3329 ({p.ekxLen} bytes in all; see `VG.Spec.MlKem.ExpandedEk`)"

/-! ## ML-KEM-768 -/

/-- `vg_mlkem768_keygen_expanded(seed: *const [u8; 64], ekx: *mut [u8; 10432], dk: *mut [u8; 2400], scratch: *mut [u64; 4096]) -> u32`. -/
def keyGenExpandedSig : Sig where
  params := [("seed", .array false .u8 64), ("ekx", .array true .u8 10432),
    ("dk", .array true .u8 2400), ("scratch", .array true .u64 4096)]
  ret := some .u32

/-- `vg_mlkem768_expand_ek(ek: *const [u8; 1184], ekx: *mut [u8; 10432], scratch: *mut [u64; 4096]) -> u32`. -/
def expandEkSig : Sig where
  params := [("ek", .array false .u8 1184), ("ekx", .array true .u8 10432),
    ("scratch", .array true .u64 4096)]
  ret := some .u32

/-- `vg_mlkem768_encaps_expanded(ekx: *const [u8; 10432], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1088], scratch: *mut [u64; 4096])`. -/
def encapsExpandedSig : Sig where
  params := [("ekx", .array false .u8 10432), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 1088), ("scratch", .array true .u64 4096)]

/-- `vg_mlkem768_decaps_expanded(dk: *const [u8; 2400], ekx: *const [u8; 10432], ct: *const [u8; 1088], key: *mut [u8; 32], scratch: *mut [u64; 4096])`. -/
def decapsExpandedSig : Sig where
  params := [("dk", .array false .u8 2400), ("ekx", .array false .u8 10432),
    ("ct", .array false .u8 1088), ("key", .array true .u8 32), ("scratch", .array true .u64 4096)]

theorem ekxLen768 : mlKem768.ekxLen = 10432 := rfl

/-- `vg_mlkem768_keygen_expanded`: see `KeyGenExpandedPost`. May leak `ρ`. -/
def keyGenExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyGenExpandedSig.contract A
    (post := fun seed ekx dk _scratch m m' r => KeyGenExpandedPost mlKem768 seed ekx dk m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ekx _dk _scratch m => leakRho (keyGenRho mlKem768 (bytesAt m seed 32)))

/-- `vg_mlkem768_expand_ek`: see `ExpandEkPost`. May leak `ρ`. -/
def expandEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandEkSig.contract A
    (post := fun ek ekx _scratch m m' r => ExpandEkPost mlKem768 ek ekx m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _ekx _scratch m => leakRho (ekRho mlKem768 (bytesAt m ek 1184)))

/-- `vg_mlkem768_encaps_expanded`: if `ekx` holds the expanded key of the
encapsulation key in its first 1184 bytes, see `EncapsExpandedPost`.
Constant time. -/
def encapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsExpandedSig.contract A
    (pre := fun ekx _msg _key _ct _scratch m => ExpandedEk mlKem768 m ekx (bytesAt m ekx 1184))
    (post := fun ekx msg key ct _scratch m m' _ => EncapsExpandedPost mlKem768 ekx msg key ct m m')
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem768_decaps_expanded`: if `DecapsExpandedPre`, see
`DecapsExpandedPost`. Constant time: in particular, it does not leak whether
the ciphertext was rejected implicitly. -/
def decapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decapsExpandedSig.contract A
    (pre := fun dk ekx _ct _key _scratch m => DecapsExpandedPre mlKem768 dk ekx m)
    (post := fun dk _ekx ct key _scratch m m' _ => DecapsExpandedPost mlKem768 dk ct key m m')
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem768_keygen_expanded` on every target that has it. -/
def keyGenExpandedApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_keygen_expanded"
  sig := keyGenExpandedSig
  writeArgs := true
  contracts := some fun A stack => keyGenExpandedContract A stack
  summary := "ML-KEM-768 key generation from a seed, `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 \
    Algorithm 16), as `vg_mlkem768_keygen`, with the encapsulation key written to `*ekx` as " ++
    ekxDoc mlKem768 "ML-KEM-768" ++ ", and the decapsulation key to `*dk`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem.keyGenExpandedContract`. Constant time but for `ρ`: timing may \
    depend on the pointers and on `ρ` (bytes 1152–1183 of `*ekx`), but not on anything else of \
    the seed or the keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 203 §3.3), or a seed so generated \
      before.",
    scratchSafety]

/-- `vg_mlkem768_expand_ek` on every target that has it. -/
def expandEkApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_expand_ek"
  sig := expandEkSig
  writeArgs := true
  contracts := some fun A stack => expandEkContract A stack
  summary := "Writes to `*ekx` " ++ ekxDoc mlKem768 "ML-KEM-768" ++ ", of the encapsulation key \
    `*ek`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem.expandEkContract`. Constant time but for `ρ`: timing may depend \
    on the pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the \
    key."
  safety := [
    "`ek` must have passed `vg_mlkem768_check_ek` (FIPS 203 §7.2).",
    scratchSafety]

/-- `vg_mlkem768_encaps_expanded` on every target that has it. -/
def encapsExpandedApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_encaps_expanded"
  sig := encapsExpandedSig
  writeArgs := true
  contracts := some fun A stack => encapsExpandedContract A stack
  summary := "ML-KEM-768 encapsulation with given randomness, `ML-KEM.Encaps_internal(ek, m)` \
    (FIPS 203 Algorithm 17), from `*ekx`, " ++ ekxDoc mlKem768 "ML-KEM-768" ++ " of `ek`, and \
    the randomness `*m`: writes the shared secret key to `*key` and the ciphertext to `*ct`. It \
    samples nothing, so it cannot fail.\n\n\
    Contract: `VG.Spec.MlKem.encapsExpandedContract`. Constant time: only the pointers may \
    affect timing."
  safety := [
    "`ekx` must have been written by `vg_mlkem768_keygen_expanded`, or by \
      `vg_mlkem768_expand_ek` from an encapsulation key that passed `vg_mlkem768_check_ek` \
      (FIPS 203 §7.2), and not changed since.",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafety]

/-- `vg_mlkem768_decaps_expanded` on every target that has it. -/
def decapsExpandedApi : Api where
  module := "mlkem768"
  name := "vg_mlkem768_decaps_expanded"
  sig := decapsExpandedSig
  writeArgs := true
  contracts := some fun A stack => decapsExpandedContract A stack
  summary := "ML-KEM-768 decapsulation, `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm \
    18), with `*ekx`, " ++ ekxDoc mlKem768 "ML-KEM-768" ++ " of the encapsulation key in the \
    decapsulation key `*dk` (its bytes 1152–2335), and the ciphertext `*ct`: writes the shared \
    secret key to `*key`, which is the implicit rejection key `J(z ‖ c)` if the ciphertext does \
    not re-encrypt to itself. It samples nothing, so it cannot fail.\n\n\
    Contract: `VG.Spec.MlKem.decapsExpandedContract`. Constant time: only the pointers may \
    affect timing; in particular, not whether the ciphertext was rejected."
  safety := [
    "`dk` must have been written by `vg_mlkem768_keygen_expanded` or `vg_mlkem768_keygen` (so \
      that it passes the checks of FIPS 203 §7.3).",
    "`ekx` must have been written by `vg_mlkem768_keygen_expanded` with `dk`, or by \
      `vg_mlkem768_expand_ek` from the encapsulation key in `dk`, and not changed since.",
    scratchSafety]

end VG.Spec.MlKem

namespace VG.Spec.MlKem1024

open Spec.MlKem
open Sha3 (bytesAt)

/-! ## ML-KEM-1024 -/

/-- `vg_mlkem1024_keygen_expanded(seed: *const [u8; 64], ekx: *mut [u8; 17984], dk: *mut [u8; 3168], scratch: *mut [u64; 6144]) -> u32`. -/
def keyGenExpandedSig : Sig where
  params := [("seed", .array false .u8 64), ("ekx", .array true .u8 17984),
    ("dk", .array true .u8 3168), ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- `vg_mlkem1024_expand_ek(ek: *const [u8; 1568], ekx: *mut [u8; 17984], scratch: *mut [u64; 6144]) -> u32`. -/
def expandEkSig : Sig where
  params := [("ek", .array false .u8 1568), ("ekx", .array true .u8 17984),
    ("scratch", .array true .u64 6144)]
  ret := some .u32

/-- `vg_mlkem1024_encaps_expanded(ekx: *const [u8; 17984], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1568], scratch: *mut [u64; 6144])`. -/
def encapsExpandedSig : Sig where
  params := [("ekx", .array false .u8 17984), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 1568), ("scratch", .array true .u64 6144)]

/-- `vg_mlkem1024_decaps_expanded(dk: *const [u8; 3168], ekx: *const [u8; 17984], ct: *const [u8; 1568], key: *mut [u8; 32], scratch: *mut [u64; 6144])`. -/
def decapsExpandedSig : Sig where
  params := [("dk", .array false .u8 3168), ("ekx", .array false .u8 17984),
    ("ct", .array false .u8 1568), ("key", .array true .u8 32), ("scratch", .array true .u64 6144)]

theorem ekxLen1024 : mlKem1024.ekxLen = 17984 := rfl

/-- `vg_mlkem1024_keygen_expanded`: see `KeyGenExpandedPost`. May leak `ρ`. -/
def keyGenExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keyGenExpandedSig.contract A
    (post := fun seed ekx dk _scratch m m' r => KeyGenExpandedPost mlKem1024 seed ekx dk m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ekx _dk _scratch m => leakRho (keyGenRho mlKem1024 (bytesAt m seed 32)))

/-- `vg_mlkem1024_expand_ek`: see `ExpandEkPost`. May leak `ρ`. -/
def expandEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandEkSig.contract A
    (post := fun ek ekx _scratch m m' r => ExpandEkPost mlKem1024 ek ekx m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _ekx _scratch m => leakRho (ekRho mlKem1024 (bytesAt m ek 1568)))

/-- `vg_mlkem1024_encaps_expanded`: if `ekx` holds the expanded key of the
encapsulation key in its first 1568 bytes, see `EncapsExpandedPost`.
Constant time. -/
def encapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsExpandedSig.contract A
    (pre := fun ekx _msg _key _ct _scratch m => ExpandedEk mlKem1024 m ekx (bytesAt m ekx 1568))
    (post := fun ekx msg key ct _scratch m m' _ => EncapsExpandedPost mlKem1024 ekx msg key ct m m')
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem1024_decaps_expanded`: if `DecapsExpandedPre`, see
`DecapsExpandedPost`. Constant time: in particular, it does not leak whether
the ciphertext was rejected implicitly. -/
def decapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decapsExpandedSig.contract A
    (pre := fun dk ekx _ct _key _scratch m => DecapsExpandedPre mlKem1024 dk ekx m)
    (post := fun dk _ekx ct key _scratch m m' _ => DecapsExpandedPost mlKem1024 dk ct key m m')
    (writeArgs := true)
    (stack := stack)

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

/-- What the documentation says of an expanded encapsulation key. -/
private def ekxDoc : String :=
  "an expanded encapsulation key of ML-KEM-1024: the encapsulation key (1568 bytes), then \
    `H(ek)` (32 bytes), then the matrix `Â` sampled from its `ρ` (FIPS 203 Algorithm 14, \
    lines 4–8), row by row, each entry as 256 little-endian `u32` coefficients less than `q` \
    = 3329 (17984 bytes in all; see `VG.Spec.MlKem.ExpandedEk`)"

/-- `vg_mlkem1024_keygen_expanded` on every target that has it. -/
def keyGenExpandedApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_keygen_expanded"
  sig := keyGenExpandedSig
  writeArgs := true
  contracts := some fun A stack => keyGenExpandedContract A stack
  summary := "ML-KEM-1024 key generation from a seed, `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 \
    Algorithm 16), as `vg_mlkem1024_keygen`, with the encapsulation key written to `*ekx` as " ++
    ekxDoc ++ ", and the decapsulation key to `*dk`. " ++ outcomeDoc ++ "\n\n\
    Contract: `VG.Spec.MlKem1024.keyGenExpandedContract`. Constant time but for `ρ`: timing may \
    depend on the pointers and on `ρ` (bytes 1536–1567 of `*ekx`), but not on anything else of \
    the seed or the keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 203 §3.3), or a seed so generated \
      before.",
    scratchSafety]

/-- `vg_mlkem1024_expand_ek` on every target that has it. -/
def expandEkApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_expand_ek"
  sig := expandEkSig
  writeArgs := true
  contracts := some fun A stack => expandEkContract A stack
  summary := "Writes to `*ekx` " ++ ekxDoc ++ ", of the encapsulation key `*ek`. " ++ outcomeDoc ++
    "\n\n\
    Contract: `VG.Spec.MlKem1024.expandEkContract`. Constant time but for `ρ`: timing may depend \
    on the pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the \
    key."
  safety := [
    "`ek` must have passed `vg_mlkem1024_check_ek` (FIPS 203 §7.2).",
    scratchSafety]

/-- `vg_mlkem1024_encaps_expanded` on every target that has it. -/
def encapsExpandedApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_encaps_expanded"
  sig := encapsExpandedSig
  writeArgs := true
  contracts := some fun A stack => encapsExpandedContract A stack
  summary := "ML-KEM-1024 encapsulation with given randomness, `ML-KEM.Encaps_internal(ek, m)` \
    (FIPS 203 Algorithm 17), from `*ekx`, " ++ ekxDoc ++ " of `ek`, and the randomness `*m`: \
    writes the shared secret key to `*key` and the ciphertext to `*ct`. It samples nothing, so \
    it cannot fail.\n\n\
    Contract: `VG.Spec.MlKem1024.encapsExpandedContract`. Constant time: only the pointers may \
    affect timing."
  safety := [
    "`ekx` must have been written by `vg_mlkem1024_keygen_expanded`, or by \
      `vg_mlkem1024_expand_ek` from an encapsulation key that passed `vg_mlkem1024_check_ek` \
      (FIPS 203 §7.2), and not changed since.",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafety]

/-- `vg_mlkem1024_decaps_expanded` on every target that has it. -/
def decapsExpandedApi : Api where
  module := "mlkem1024"
  name := "vg_mlkem1024_decaps_expanded"
  sig := decapsExpandedSig
  writeArgs := true
  contracts := some fun A stack => decapsExpandedContract A stack
  summary := "ML-KEM-1024 decapsulation, `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm \
    18), with `*ekx`, " ++ ekxDoc ++ " of the encapsulation key in the decapsulation key `*dk` \
    (its bytes 1536–3103), and the ciphertext `*ct`: writes the shared secret key to `*key`, \
    which is the implicit rejection key `J(z ‖ c)` if the ciphertext does not re-encrypt to \
    itself. It samples nothing, so it cannot fail.\n\n\
    Contract: `VG.Spec.MlKem1024.decapsExpandedContract`. Constant time: only the pointers may \
    affect timing; in particular, not whether the ciphertext was rejected."
  safety := [
    "`dk` must have been written by `vg_mlkem1024_keygen_expanded` or `vg_mlkem1024_keygen` \
      (so that it passes the checks of FIPS 203 §7.3).",
    "`ekx` must have been written by `vg_mlkem1024_keygen_expanded` with `dk`, or by \
      `vg_mlkem1024_expand_ek` from the encapsulation key in `dk`, and not changed since.",
    scratchSafety]

end VG.Spec.MlKem1024
