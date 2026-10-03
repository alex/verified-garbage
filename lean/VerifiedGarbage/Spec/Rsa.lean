import VerifiedGarbage.TCB.Mem

/-!
# RSA primitives (RFC 8017 §§4–5, NIST SP 800-56B Rev. 2)

**Trusted** (as every file in `Spec/`). The RSA primitives of PKCS #1 v2.2
(RFC 8017), for a two-prime key, on octet strings:

* `publicOp`: RSAEP (§5.1.1), which is also RSAVP1 (§5.2.2):
  `c = m^e mod n`, an error if `m` is not in `[0, n-1]`.
* `privateCrt`: RSADP (§5.1.2), which is also RSASP1 (§5.2.1), with the
  private key in the second form of §3.2, `(p, q, dP, dQ, qInv)`: step 2.b,
  with `u = 2`.
* `privatePrimes`: the same with the private key in SP 800-56B's
  prime-factor format `(p, q, d)` (§6.2.2): the CRT values are
  `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p`, as
  §6.2.2's CRT format defines them, and an error if `q` has no inverse
  modulo `p`.
* `privateExponents`: the same with the private key in SP 800-56B's basic
  format `(n, e, d)` (§6.2.2): `p` and `q` are recovered by Appendix C.1
  (`recoverPrimes`), and then as `privatePrimes`.

Integers are naturals, converted from and to octet strings by OS2IP and
I2OSP (§4), most significant octet first. The modulus `n` is given as its
`k` octets, and every result is `k` octets.

Every primitive checks what it can afford to: the modulus is odd and from 512
to 8192 bits, its first octet is not zero (so `k` is its length in octets),
the input is below `n`, and the factors' product is `n`. Nothing checks that
`p` and `q` are prime or that the exponents match `e`. For a valid RSA key
(distinct primes, `e·d ≡ 1 (mod λ(n))`, and CRT values as §6.2.2 defines
them) the three private forms all compute `c^d mod n`, but for the rare key
whose factors `recoverPrimes` does not find (Appendix C.1, note 1); for any
other key they compute exactly what is written here.

Padding (EME-OAEP, EMSA-PSS, PKCS #1 v1.5) is a separate layer.
-/

namespace VG.Spec.Rsa

/-! ## Integers and octet strings (§4) -/

/-- OS2IP (§4.2): an octet string as an integer, most significant octet
first. -/
def os2ip (bs : List Byte) : Nat := bs.foldl (fun x b => 256 * x + b.toNat) 0

/-- I2OSP (§4.1): `x` as `xLen` octets, most significant first. §4.1 gives an
error if `x ≥ 256^xLen`; every integer converted here is below the modulus,
which is below `256^xLen`, so this keeps only the low `xLen` octets. -/
def i2osp (x xLen : Nat) : List Byte :=
  (List.range xLen).map fun i => BitVec.ofNat 8 (x / 256 ^ (xLen - 1 - i))

/-! ## Arithmetic -/

/-- `a^e mod m`, by square-and-multiply. -/
def powMod (a e m : Nat) : Nat :=
  if e = 0 then 1 % m else
    let t := powMod a (e / 2) m
    let u := t * t % m
    if e % 2 = 0 then u else u * a % m
termination_by e
decreasing_by omega

/-- Extended Euclid: from `r' = a s' + b t'` and `r = a s + b t`, the same for
`r' = gcd`. -/
def xgcd (r : Nat) (s : Int) (r' : Nat) (s' : Int) : Nat × Int :=
  if r = 0 then (r', s') else xgcd (r' % r) (s' - (r' / r : Nat) * s) r s
termination_by r
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The inverse of `a` modulo `m > 1`: the `x < m` with `a x ≡ 1 (mod m)`,
which exists exactly when `gcd(a, m) = 1` and is then unique; `none` if there
is none. It is found by the extended Euclidean algorithm, and checked. -/
def inverse (a m : Nat) : Option Nat :=
  let x := ((xgcd (a % m) 1 m 0).2 % (m : Int)).toNat
  if a * x % m = 1 then some x else none

/-! ## The modulus -/

/-- A modulus the primitives take, given as `k` octets: odd, from 512 to
8192 bits, and `k` octets long (its first octet is not zero). -/
def modulusValid (n k : Nat) : Bool :=
  n % 2 == 1 && 2 ^ 511 ≤ n && n < 2 ^ 8192 && 256 ^ (k - 1) ≤ n

/-! ## The primitives on integers -/

/-- RSAEP (§5.1.1) and RSAVP1 (§5.2.2): `x^e mod n`, or `none` if `x` is not
in `[0, n-1]`. -/
def encrypt (n e x : Nat) : Option Nat :=
  if x < n then some (powMod x e n) else none

/-- RSADP (§5.1.2) and RSASP1 (§5.2.1) with the private key
`(p, q, dP, dQ, qInv)` (§3.2's second form, two primes), or `none` if `c` is
not in `[0, n-1]`, `p q ≠ n` or `qInv` is not in `[0, p-1]`. Step 2.b:
`m_1 = c^dP mod p`, `m_2 = c^dQ mod q`, `h = (m_1 - m_2) qInv mod p`, and
`m = m_2 + q h`. -/
def decryptCrt (n p q dP dQ qInv c : Nat) : Option Nat :=
  if c < n ∧ p * q = n ∧ qInv < p then
    let m₁ := powMod c dP p
    let m₂ := powMod c dQ q
    let h := (((m₁ : Int) - m₂) * qInv % (p : Int)).toNat
    some (m₂ + q * h)
  else none

/-- SP 800-56B Rev. 2 §6.2.2's CRT values of the private key `(p, q, d)`:
`(dP, dQ, qInv)` with `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and
`qInv = q⁻¹ mod p`, or `none` if `q` has no inverse modulo `p`. -/
def crtValues (p q d : Nat) : Option (Nat × Nat × Nat) :=
  (inverse q p).map fun qInv => (d % (p - 1), d % (q - 1), qInv)

/-- `m = 2^t r` with `r` odd, for `m > 0`: `(t, r)`. -/
def splitTwos (m : Nat) : Nat × Nat :=
  if m = 0 ∨ m % 2 = 1 then (0, m) else
    let (t, r) := splitTwos (m / 2)
    (t + 1, r)
termination_by m
decreasing_by omega

/-- Steps 3.b–3.f of SP 800-56B Rev. 2 Appendix C.1 for the candidate `g`:
`some y` if they go to step 5 with `y`, `none` if they go to step 3.g. -/
def recoverStep (n t r g : Nat) : Option Nat :=
  let y := powMod g r n
  -- Step 3.c.
  if y = 1 ∨ y = n - 1 then none else squarings (t - 1) y
where
  /-- Step 3.d's `j` loop with `j` iterations left, then steps 3.e and 3.f. -/
  squarings : Nat → Nat → Option Nat
    | 0, y => if y * y % n = 1 then some y else none
    | j + 1, y =>
      let x := y * y % n
      if x = 1 then some y else if x = n - 1 then none else squarings j x

/-- The most candidates `recoverPrimes` tries: step 3's bound. -/
def recoverTries : Nat := 100

/-- SP 800-56B Rev. 2 Appendix C.1, `RecoverPrimeFactors(n, e, d)`: the prime
factors `(p, q)` of `n`, with `p > q`, or `none` ("prime factors not found");
and the number of candidates `g` tried.

Step 3.a generates a random `g` in `[0, n-1]`. Here the `i`-th candidate is
`g = i + 1`, so the result is a function of the key. For a valid key each
candidate reveals the factors with probability at least 1/2 (Appendix C.1,
note 1), so a key whose factors are not found is invalid but for a
negligible fraction of keys. Step 5's `p = GCD(y - 1, n)` and `q = n / p`
are ordered so that `p > q`, as Appendix C.2 orders them (note 3 of either
says the order is arbitrary). -/
def recoverPrimes (n e d : Nat) : Option (Nat × Nat) × Nat :=
  -- Step 1: `m = de - 1`, which must be positive (for `t ≥ 1`) and even.
  if d * e < 2 ∨ (d * e - 1) % 2 = 1 then (none, 0) else
    -- Step 2.
    let (t, r) := splitTwos (d * e - 1)
    -- Step 3, for `i` from 1 to `recoverTries`.
    let rec go : Nat → Option (Nat × Nat) × Nat
      | 0 => (none, recoverTries)
      | k + 1 =>
        let i := recoverTries - k
        match recoverStep n t r (i + 1) with
        | some y =>
          -- Step 5.
          let p := Nat.gcd (y - 1) n
          let q := n / p
          (some (max p q, min p q), i)
        | none => go k
    go recoverTries

/-! ## The primitives on octet strings

The modulus `n` is `k` octets (OS2IP of `nB`, `k = nB.length`), and so are
the input and the result. -/

/-- RSAEP and RSAVP1 of the input `xB` with the public key `(nB, eB)`:
`some` result, or `none` if the modulus is not valid or the input is not
below it. -/
def publicOp (nB eB xB : List Byte) : Option (List Byte) :=
  let n := os2ip nB
  if modulusValid n nB.length then
    (encrypt n (os2ip eB) (os2ip xB)).map (i2osp · nB.length)
  else none

/-- RSADP and RSASP1 of the input `xB` with the private key
`(p, q, dP, dQ, qInv)` of the modulus `nB`: `some` result, or `none` if the
modulus is not valid, the input is not below it, `p q ≠ n`, or `qInv ≥ p`. -/
def privateCrt (nB xB pB qB dPB dQB qInvB : List Byte) : Option (List Byte) :=
  let n := os2ip nB
  if modulusValid n nB.length then
    (decryptCrt n (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB) (os2ip qInvB)
      (os2ip xB)).map (i2osp · nB.length)
  else none

/-- `privateCrt` with the CRT values of `(p, q, d)` (`crtValues`), or `none`
if `q` has no inverse modulo `p`. -/
def privatePrimesInt (n p q d c : Nat) : Option Nat := do
  let (dP, dQ, qInv) ← crtValues p q d
  decryptCrt n p q dP dQ qInv c

/-- RSADP and RSASP1 of the input `xB` with the private key `(p, q, d)` of
the modulus `nB`: `some` result, or `none` if the modulus is not valid, the
input is not below it, `p q ≠ n`, or `q` has no inverse modulo `p`. -/
def privatePrimes (nB xB pB qB dB : List Byte) : Option (List Byte) :=
  let n := os2ip nB
  if modulusValid n nB.length then
    (privatePrimesInt n (os2ip pB) (os2ip qB) (os2ip dB) (os2ip xB)).map (i2osp · nB.length)
  else none

/-- RSADP and RSASP1 of the input `xB` with the private key `(nB, eB, dB)`:
`some` result, or `none` if the modulus is not valid, its factors are not
found (`recoverPrimes`), the input is not below it, or `q` has no inverse
modulo `p`; and the number of candidates `recoverPrimes` tried (0 if the
modulus is not valid). -/
def privateExponents (nB eB xB dB : List Byte) : Option (List Byte) × Nat :=
  let n := os2ip nB
  if modulusValid n nB.length then
    match recoverPrimes n (os2ip eB) (os2ip dB) with
    | (some (p, q), tries) =>
      ((privatePrimesInt n p q (os2ip dB) (os2ip xB)).map (i2osp · nB.length), tries)
    | (none, tries) => (none, tries)
  else (none, 0)

end VG.Spec.Rsa
