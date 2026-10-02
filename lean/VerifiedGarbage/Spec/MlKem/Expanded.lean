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

/-- What the documentation says of an expanded encapsulation key. -/
private def ekxDoc (p : Params) : String :=
  s!"an expanded encapsulation key of {p.name}: the encapsulation key ({p.ekLen} bytes), then \
    `H(ek)` (32 bytes), then the matrix `Â` sampled from its `ρ` (FIPS 203 Algorithm 14, \
    lines 4–8), row by row, each entry as 256 little-endian `u32` coefficients less than `q` \
    = 3329 ({p.ekxLen} bytes in all; see `VG.Spec.MlKem.ExpandedEk`)"

/-! ## Any parameter set, with `scratch` words of working space -/

/-- `vg_mlkem*_keygen_expanded(seed: *const [u8; 64], ekx: *mut [u8; ekxLen], dk: *mut [u8; dkLen], scratch: *mut [u64; scratch]) -> u32`. -/
def Params.keyGenExpandedSig (p : Params) (scratch : Nat) : Sig where
  params := [("seed", .array false .u8 64), ("ekx", .array true .u8 p.ekxLen),
    ("dk", .array true .u8 p.dkLen), ("scratch", .array true .u64 scratch)]
  ret := some .u32

/-- `vg_mlkem*_expand_ek(ek: *const [u8; ekLen], ekx: *mut [u8; ekxLen], scratch: *mut [u64; scratch]) -> u32`. -/
def Params.expandEkSig (p : Params) (scratch : Nat) : Sig where
  params := [("ek", .array false .u8 p.ekLen), ("ekx", .array true .u8 p.ekxLen),
    ("scratch", .array true .u64 scratch)]
  ret := some .u32

/-- `vg_mlkem*_encaps_expanded(ekx: *const [u8; ekxLen], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; ctLen], scratch: *mut [u64; scratch])`. -/
def Params.encapsExpandedSig (p : Params) (scratch : Nat) : Sig where
  params := [("ekx", .array false .u8 p.ekxLen), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 p.ctLen),
    ("scratch", .array true .u64 scratch)]

/-- `vg_mlkem*_decaps_expanded(dk: *const [u8; dkLen], ekx: *const [u8; ekxLen], ct: *const [u8; ctLen], key: *mut [u8; 32], scratch: *mut [u64; scratch])`. -/
def Params.decapsExpandedSig (p : Params) (scratch : Nat) : Sig where
  params := [("dk", .array false .u8 p.dkLen), ("ekx", .array false .u8 p.ekxLen),
    ("ct", .array false .u8 p.ctLen), ("key", .array true .u8 32),
    ("scratch", .array true .u64 scratch)]

/-- `vg_mlkem*_keygen_expanded`: see `KeyGenExpandedPost`. May leak `ρ`. -/
def Params.keyGenExpandedContract (p : Params) (scratch : Nat) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (p.keyGenExpandedSig scratch).contract A
    (post := fun seed ekx dk _scratch m m' r => KeyGenExpandedPost p seed ekx dk m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ekx _dk _scratch m => leakRho (keyGenRho p (bytesAt m seed 32)))

/-- `vg_mlkem*_expand_ek`: see `ExpandEkPost`. May leak `ρ`. -/
def Params.expandEkContract (p : Params) (scratch : Nat) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (p.expandEkSig scratch).contract A
    (post := fun ek ekx _scratch m m' r => ExpandEkPost p ek ekx m m' r)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _ekx _scratch m => leakRho (ekRho p (bytesAt m ek p.ekLen)))

/-- `vg_mlkem*_encaps_expanded`: if `ekx` holds the expanded key of the
encapsulation key in its first `384k + 32` bytes, see `EncapsExpandedPost`.
Constant time. -/
def Params.encapsExpandedContract (p : Params) (scratch : Nat) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (p.encapsExpandedSig scratch).contract A
    (pre := fun ekx _msg _key _ct _scratch m => ExpandedEk p m ekx (bytesAt m ekx p.ekLen))
    (post := fun ekx msg key ct _scratch m m' _ => EncapsExpandedPost p ekx msg key ct m m')
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem*_decaps_expanded`: if `DecapsExpandedPre`, see
`DecapsExpandedPost`. Constant time: in particular, it does not leak whether
the ciphertext was rejected implicitly. -/
def Params.decapsExpandedContract (p : Params) (scratch : Nat) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (p.decapsExpandedSig scratch).contract A
    (pre := fun dk ekx _ct _key _scratch m => DecapsExpandedPre p dk ekx m)
    (post := fun dk _ekx ct key _scratch m m' _ => DecapsExpandedPost p dk ct key m m')
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem*_keygen_expanded` on every target that has it, whose contract
is `keyGenExpandedContract` of the namespace `ns`. -/
def Params.keyGenExpandedApi (p : Params) (scratch : Nat) (ns : String) : Api where
  module := p.module
  name := p.fn "keygen_expanded"
  sig := p.keyGenExpandedSig scratch
  writeArgs := true
  contracts := some fun A stack => p.keyGenExpandedContract scratch A stack
  summary := s!"{p.name} key generation from a seed, `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 \
    Algorithm 16), as `{p.fn "keygen"}`, with the encapsulation key written to `*ekx` as " ++
    ekxDoc p ++ ", and the decapsulation key to `*dk`. " ++ outcomeDoc ++ s!"\n\n\
    Contract: `{ns}.keyGenExpandedContract`. Constant time but for `ρ`: timing may depend on \
    the pointers and on `ρ` (bytes {384 * p.k}–{384 * p.k + 31} of `*ekx`), but not on \
    anything else of the seed or the keys."
  safety := [
    "`seed` must be random bytes from an approved RBG (FIPS 203 §3.3), or a seed so generated \
      before.",
    scratchSafetyDoc]

/-- `vg_mlkem*_expand_ek` on every target that has it, whose contract is
`expandEkContract` of the namespace `ns`. -/
def Params.expandEkApi (p : Params) (scratch : Nat) (ns : String) : Api where
  module := p.module
  name := p.fn "expand_ek"
  sig := p.expandEkSig scratch
  writeArgs := true
  contracts := some fun A stack => p.expandEkContract scratch A stack
  summary := "Writes to `*ekx` " ++ ekxDoc p ++ ", of the encapsulation key `*ek`. " ++
    outcomeDoc ++ s!"\n\n\
    Contract: `{ns}.expandEkContract`. Constant time but for `ρ`: timing may depend on the \
    pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the key."
  safety := [
    s!"`ek` must have passed `{p.fn "check_ek"}` (FIPS 203 §7.2).",
    scratchSafetyDoc]

/-- `vg_mlkem*_encaps_expanded` on every target that has it, whose contract
is `encapsExpandedContract` of the namespace `ns`. -/
def Params.encapsExpandedApi (p : Params) (scratch : Nat) (ns : String) : Api where
  module := p.module
  name := p.fn "encaps_expanded"
  sig := p.encapsExpandedSig scratch
  writeArgs := true
  contracts := some fun A stack => p.encapsExpandedContract scratch A stack
  summary := s!"{p.name} encapsulation with given randomness, `ML-KEM.Encaps_internal(ek, m)` \
    (FIPS 203 Algorithm 17), from `*ekx`, " ++ ekxDoc p ++ " of `ek`, and the randomness `*m`: \
    writes the shared secret key to `*key` and the ciphertext to `*ct`. It samples nothing, so \
    it cannot fail." ++ s!"\n\n\
    Contract: `{ns}.encapsExpandedContract`. Constant time: only the pointers may affect \
    timing."
  safety := [
    s!"`ekx` must have been written by `{p.fn "keygen_expanded"}`, or by \
      `{p.fn "expand_ek"}` from an encapsulation key that passed `{p.fn "check_ek"}` \
      (FIPS 203 §7.2), and not changed since.",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafetyDoc]

/-- `vg_mlkem*_decaps_expanded` on every target that has it, whose contract
is `decapsExpandedContract` of the namespace `ns`. -/
def Params.decapsExpandedApi (p : Params) (scratch : Nat) (ns : String) : Api where
  module := p.module
  name := p.fn "decaps_expanded"
  sig := p.decapsExpandedSig scratch
  writeArgs := true
  contracts := some fun A stack => p.decapsExpandedContract scratch A stack
  summary := s!"{p.name} decapsulation, `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm \
    18), with `*ekx`, " ++ ekxDoc p ++ s!" of the encapsulation key in the decapsulation key \
    `*dk` (its bytes {384 * p.k}–{768 * p.k + 31}), and the ciphertext `*ct`: writes the shared \
    secret key to `*key`, which is the implicit rejection key `J(z ‖ c)` if the ciphertext does \
    not re-encrypt to itself. It samples nothing, so it cannot fail.\n\n\
    Contract: `{ns}.decapsExpandedContract`. Constant time: only the pointers may affect \
    timing; in particular, not whether the ciphertext was rejected."
  safety := [
    s!"`dk` must have been written by `{p.fn "keygen_expanded"}` or `{p.fn "keygen"}` (so \
      that it passes the checks of FIPS 203 §7.3).",
    s!"`ekx` must have been written by `{p.fn "keygen_expanded"}` with `dk`, or by \
      `{p.fn "expand_ek"}` from the encapsulation key in `dk`, and not changed since.",
    scratchSafetyDoc]

/-! ## ML-KEM-768 -/

theorem ekxLen768 : mlKem768.ekxLen = 10432 := rfl

/-- The signature of `vg_mlkem768_keygen_expanded`. -/
def keyGenExpandedSig : Sig := mlKem768.keyGenExpandedSig 4096

/-- The signature of `vg_mlkem768_expand_ek`. -/
def expandEkSig : Sig := mlKem768.expandEkSig 4096

/-- The signature of `vg_mlkem768_encaps_expanded`. -/
def encapsExpandedSig : Sig := mlKem768.encapsExpandedSig 4096

/-- The signature of `vg_mlkem768_decaps_expanded`. -/
def decapsExpandedSig : Sig := mlKem768.decapsExpandedSig 4096

/-- The contract of `vg_mlkem768_keygen_expanded`. -/
def keyGenExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem768.keyGenExpandedContract 4096 A stack

/-- The contract of `vg_mlkem768_expand_ek`. -/
def expandEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem768.expandEkContract 4096 A stack

/-- The contract of `vg_mlkem768_encaps_expanded`. -/
def encapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem768.encapsExpandedContract 4096 A stack

/-- The contract of `vg_mlkem768_decaps_expanded`. -/
def decapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem768.decapsExpandedContract 4096 A stack

/-- `vg_mlkem768_keygen_expanded` on every target that has it. -/
def keyGenExpandedApi : Api := mlKem768.keyGenExpandedApi 4096 "VG.Spec.MlKem"

/-- `vg_mlkem768_expand_ek` on every target that has it. -/
def expandEkApi : Api := mlKem768.expandEkApi 4096 "VG.Spec.MlKem"

/-- `vg_mlkem768_encaps_expanded` on every target that has it. -/
def encapsExpandedApi : Api := mlKem768.encapsExpandedApi 4096 "VG.Spec.MlKem"

/-- `vg_mlkem768_decaps_expanded` on every target that has it. -/
def decapsExpandedApi : Api := mlKem768.decapsExpandedApi 4096 "VG.Spec.MlKem"

end VG.Spec.MlKem

namespace VG.Spec.MlKem1024

open Spec.MlKem

/-! ## ML-KEM-1024 -/

theorem ekxLen1024 : mlKem1024.ekxLen = 17984 := rfl

/-- The signature of `vg_mlkem1024_keygen_expanded`. -/
def keyGenExpandedSig : Sig := mlKem1024.keyGenExpandedSig 6144

/-- The signature of `vg_mlkem1024_expand_ek`. -/
def expandEkSig : Sig := mlKem1024.expandEkSig 6144

/-- The signature of `vg_mlkem1024_encaps_expanded`. -/
def encapsExpandedSig : Sig := mlKem1024.encapsExpandedSig 6144

/-- The signature of `vg_mlkem1024_decaps_expanded`. -/
def decapsExpandedSig : Sig := mlKem1024.decapsExpandedSig 6144

/-- The contract of `vg_mlkem1024_keygen_expanded`. -/
def keyGenExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem1024.keyGenExpandedContract 6144 A stack

/-- The contract of `vg_mlkem1024_expand_ek`. -/
def expandEkContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem1024.expandEkContract 6144 A stack

/-- The contract of `vg_mlkem1024_encaps_expanded`. -/
def encapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem1024.encapsExpandedContract 6144 A stack

/-- The contract of `vg_mlkem1024_decaps_expanded`. -/
def decapsExpandedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  mlKem1024.decapsExpandedContract 6144 A stack

/-- `vg_mlkem1024_keygen_expanded` on every target that has it. -/
def keyGenExpandedApi : Api := mlKem1024.keyGenExpandedApi 6144 "VG.Spec.MlKem1024"

/-- `vg_mlkem1024_expand_ek` on every target that has it. -/
def expandEkApi : Api := mlKem1024.expandEkApi 6144 "VG.Spec.MlKem1024"

/-- `vg_mlkem1024_encaps_expanded` on every target that has it. -/
def encapsExpandedApi : Api := mlKem1024.encapsExpandedApi 6144 "VG.Spec.MlKem1024"

/-- `vg_mlkem1024_decaps_expanded` on every target that has it. -/
def decapsExpandedApi : Api := mlKem1024.decapsExpandedApi 6144 "VG.Spec.MlKem1024"

end VG.Spec.MlKem1024
