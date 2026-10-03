import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.TCB.Artifact

/-!
# RSA primitives: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa`:

* `vg_rsa_public`: RSAEP and RSAVP1 (`Rsa.publicOp`);
* `vg_rsa_private_crt`: RSADP and RSASP1 with the private key
  `(p, q, dP, dQ, qInv)` (`Rsa.privateCrt`);
* `vg_rsa_private_primes`: the same with the private key `(p, q, d)`
  (`Rsa.privatePrimes`);
* `vg_rsa_private_exponents`: the same with the private key `(n, e, d)`
  (`Rsa.privateExponents`).

Every number is a slice of octets, most significant first, with a length of
its own (a `Sig` slice carries its own length). The modulus `n` is `n_len`
octets, from 64 to 1024, and so are the input and the output; `e` and `d`
are at most `n_len` octets; `p` and its values (`dP`, `qInv`) are `p_len`
octets, and `q` and `dQ` are `q_len` octets, each below `n_len`. These are
preconditions, on the public lengths; everything about the values is
checked: the function returns 1 and writes the result to `out`, or returns
0 and writes zeros.

The signature determines memory validity, separation and that the pointers
and lengths are public, through `Sig.contract`. The public key, `n` and `e`,
is public too, and may affect timing (`leak`): an implementation may, for
instance, branch on the bits of `e`. The input is secret (RSAEP may encrypt
a secret), and so is every part of a private key. `vg_rsa_private_exponents`
may also leak how many candidates its prime-factor recovery tried, which is
1 or 2 for most keys (SP 800-56B Rev. 2 Appendix C.1, note 1). The return
value depends on secrets (whether the input is below `n`, and whether the
private key is consistent).

`scratch` is working space of at least `16 n_len` `u64`s, whose contents on
return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

namespace VG.Spec.Rsa

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The least working space, in `u64`s, for a modulus of `nLen` octets. -/
def scratchWords (nLen : Nat) : Nat := 16 * nLen

/-- The bounds on the modulus' length, in octets. -/
def lenValid (nLen : Nat) : Prop := 64 ≤ nLen ∧ nLen ≤ 1024

/-- The postcondition of a function returning `res`, `nLen` octets or
`none`, at `out`. -/
def written (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) : Option (List Byte) → Prop
  | some y => r = 1 ∧ bytesAt m' out nLen = y
  | none => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * n_len`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-! ## `vg_rsa_public` -/

/-- `vg_rsa_public(out: *mut u8, out_len: usize, n: *const u8, n_len: usize,
e: *const u8, e_len: usize, input: *const u8, input_len: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSAEP of the input with the public key `(n, e)` (`publicOp`). Constant
time but for the public key. -/
def publicContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _input inputLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen input _inputLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (publicOp (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m input nLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen _input _inputLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def publicApi : Api where
  module := "rsa"
  name := "vg_rsa_public"
  sig := publicSig
  writeArgs := true
  contracts := some fun A stack => publicContract A stack
  summary := "The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also RSAVP1 \
    (§5.2.2). With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to \
    8192 bits, its first byte not zero) and the public exponent `e` (`e_len` bytes, most \
    significant first), writes `input^e mod n` (`n_len` bytes, most significant first) to \
    `out` and returns 1; or writes zeros and returns 0 if `n` is not such a modulus or the \
    input (`n_len` bytes, most significant first) is not below `n`.\n\n\
    Contract: `VG.Spec.Rsa.publicContract`. Constant time but for the public key: timing may \
    depend on the pointers, the lengths and the contents of `n` and `e`, not on the input."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## `vg_rsa_private_crt` -/

/-- `vg_rsa_private_crt(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8,
dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def privateCrtSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("input", .slice false .u8 "input_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSADP of the input with the private key `(p, q, dP, dQ, qInv)` of the
modulus `n` (`privateCrt`). Constant time but for `n`. -/
def privateCrtContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateCrtSig.contract A
    (pre := fun _out outLen _n nLen _input inputLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv
        qinvLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen dp _dpLen dq _dqLen qinv
        _qinvLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (privateCrt (bytesAt m n nLen.toNat) (bytesAt m input nLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _dp _dpLen _dq
        _dqLen _qinv _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def privateCrtApi : Api where
  module := "rsa"
  name := "vg_rsa_private_crt"
  sig := privateCrtSig
  writeArgs := true
  contracts := some fun A stack => privateCrtContract A stack
  summary := "The RSA private-key operation: RSADP (RFC 8017 §5.1.2), which is also RSASP1 \
    (§5.2.1), with the private key `(p, q, dP, dQ, qInv)` (§3.2's second form, with two \
    primes). With the modulus `n` (`n_len` bytes, most significant first, odd, from 512 to \
    8192 bits, its first byte not zero), writes the result of step 2.b for the input \
    (`n_len` bytes, most significant first) to `out` (`n_len` bytes, most significant \
    first) and returns 1; or writes zeros and returns 0 if `n` is not such a modulus, the \
    input is not below `n`, `p q ≠ n`, or `qInv ≥ p`. `p`, `dp` and `qinv` are `p_len` \
    bytes, and `q` and `dq` are `q_len` bytes, all most significant first. For a valid RSA \
    key the result is `input^d mod n`; nothing checks that `p` and `q` are prime or that \
    the exponents match a public exponent.\n\n\
    Contract: `VG.Spec.Rsa.privateCrtContract`. Constant time but for the modulus: timing \
    may depend on the pointers, the lengths and the contents of `n`, not on the input or \
    the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

/-! ## `vg_rsa_private_primes` -/

/-- `vg_rsa_private_primes(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize,
q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def privatePrimesSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("input", .slice false .u8 "input_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("d", .slice false .u8 "d_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSADP of the input with the private key `(p, q, d)` of the modulus `n`
(`privatePrimes`). Constant time but for `n`. -/
def privatePrimesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privatePrimesSig.contract A
    (pre := fun _out outLen _n nLen _input inputLen _p pLen _q qLen _d dLen _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧ scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen input _inputLen p pLen q qLen d dLen _scratch _scratchLen
        m m' r =>
      written m' out nLen.toNat r
        (privatePrimes (bytesAt m n nLen.toNat) (bytesAt m input nLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m d dLen.toNat)))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen _input _inputLen _p _pLen _q _qLen _d _dLen _scratch
        _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def privatePrimesApi : Api where
  module := "rsa"
  name := "vg_rsa_private_primes"
  sig := privatePrimesSig
  writeArgs := true
  contracts := some fun A stack => privatePrimesContract A stack
  summary := "The RSA private-key operation: RSADP (RFC 8017 §5.1.2), which is also RSASP1 \
    (§5.2.1), with the private key `(p, q, d)` (SP 800-56B Rev. 2 §6.2.2's prime-factor \
    format), through its CRT values `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and \
    `qInv = q⁻¹ mod p` (§6.2.2's CRT format). With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), writes the \
    result for the input (`n_len` bytes, most significant first) to `out` (`n_len` bytes, \
    most significant first) and returns 1; or writes zeros and returns 0 if `n` is not such \
    a modulus, the input is not below `n`, `p q ≠ n`, or `q` has no inverse modulo `p`. `p` \
    is `p_len` bytes, `q` is `q_len` bytes and `d` is `d_len` bytes, all most significant \
    first. For a valid RSA key the result is `input^d mod n`; nothing checks that `p` and \
    `q` are prime.\n\n\
    Contract: `VG.Spec.Rsa.privatePrimesContract`. Constant time but for the modulus: \
    timing may depend on the pointers, the lengths and the contents of `n`, not on the \
    input or the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.", "`d_len` must be in 1..=`n_len`."] ++
    scratchSafety

/-! ## `vg_rsa_private_exponents` -/

/-- `vg_rsa_private_exponents(out: *mut u8, out_len: usize, n: *const u8,
n_len: usize, e: *const u8, e_len: usize, input: *const u8,
input_len: usize, d: *const u8, d_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def privateExponentsSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("n", .slice false .u8 "n_len"),
    ("e", .slice false .u8 "e_len"), ("input", .slice false .u8 "input_len"),
    ("d", .slice false .u8 "d_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- RSADP of the input with the private key `(n, e, d)`
(`privateExponents`). Constant time but for the public key and the number of
candidates the prime-factor recovery tried. -/
def privateExponentsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privateExponentsSig.contract A
    (pre := fun _out outLen _n nLen _e eLen _input inputLen _d dLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
        1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun out _outLen n nLen e eLen input _inputLen d dLen _scratch _scratchLen m m' r =>
      written m' out nLen.toNat r
        (privateExponents (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m input nLen.toNat) (bytesAt m d dLen.toNat)).1)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen n nLen e eLen input _inputLen d dLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        [(privateExponents (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
          (bytesAt m input nLen.toNat) (bytesAt m d dLen.toNat)).2])

def privateExponentsApi : Api where
  module := "rsa"
  name := "vg_rsa_private_exponents"
  sig := privateExponentsSig
  writeArgs := true
  contracts := some fun A stack => privateExponentsContract A stack
  summary := s!"The RSA private-key operation: RSADP (RFC 8017 §5.1.2), which is also RSASP1 \
    (§5.2.1), with the private key `(n, e, d)` (SP 800-56B Rev. 2 §6.2.2's basic format). \
    Recovers the prime factors `p > q` of `n` (SP 800-56B Rev. 2 Appendix C.1, with the \
    candidates `g = 2, 3, …` and at most {recoverTries} of them), then computes as \
    `vg_rsa_private_primes` does with `(p, q, d)`. With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), the public \
    exponent `e` (`e_len` bytes) and the private exponent `d` (`d_len` bytes), both most \
    significant first, writes the result for the input (`n_len` bytes, most significant \
    first) to `out` (`n_len` bytes, most significant first) and returns 1; or writes zeros \
    and returns 0 if `n` is not such a modulus, its factors are not found, the input is not \
    below `n`, or `q` has no inverse modulo `p`. For a valid RSA key the result is \
    `input^d mod n`.\n\n\
    Contract: `VG.Spec.Rsa.privateExponentsContract`. Constant time but for the public key \
    and the number of candidates the factor recovery tried (1 or 2 for most keys): timing \
    may depend on the pointers, the lengths, the contents of `n` and `e`, and that number, \
    not otherwise on the input or the private key."
  safety := ["`n_len` must be in 64..=1024.", "`out_len` and `input_len` must be `n_len`.",
    "`e_len` and `d_len` must be in 1..=`n_len`."] ++ scratchSafety

end VG.Spec.Rsa
