import Lean.Elab.Command
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-!
# RSA primitive specification tests

Known answers are parsed from the byte-for-byte NIST CAVP RSADP component
vectors (`vectors/nist-cavp-rsadp/`, SP 800-56B, 1024- and 2048-bit
moduli). Each gives `n`, `e`, `d` and `c`, and either the result `k` or the
failure for `c ≥ n`; no vector values are embedded in this test. For each:

* `privateExponents` recovers the factors of `n` (Appendix C.1) and gives
  `k`, or fails for `c ≥ n`.
* The recovered `p > q` multiply to `n`; `privatePrimes` with them and `d`
  gives `k`, and so does `privateCrt` with their CRT values (`crtValues`),
  also with `p`, `dP` and `qInv` one octet longer (a leading zero).
* `publicOp` with `e` takes `k` back to `c`.
* Inconsistent keys fail: `qInv + p`, and `q + 2` (so `p q ≠ n`).

The rest checks the edges on arithmetic inputs, not known answers: the
bounds of `modulusValid`, OS2IP and I2OSP, and that `inverse` finds every
inverse modulo small moduli.
-/

namespace VG.Test.Rsa

open Lean Elab Command Spec.Rsa

/-- A hexadecimal integer (the file prints integers without leading zeros, so
some have an odd number of digits). -/
def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (init := 0) fun x c =>
    if '0' ≤ c && c ≤ '9' then pure (16 * x + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then pure (16 * x + (c.toNat - 'a'.toNat + 10))
    else throw "invalid hex digit"

structure Vector where
  n : Nat := 0
  e : Nat := 0
  d : Nat := 0
  c : Nat := 0
  pass : Bool := false
  k : Nat := 0

/-- The vectors of `RSADPComponent800_56B.txt`: each starts at `COUNT`. -/
def parse (text : String) : Except String (List Vector) := do
  let mut v : Option Vector := none
  let mut vs := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "[" || line.startsWith "#" then continue
    match line.splitOn " = " with
    | [field, value] =>
      let value := value.trimAscii.toString
      if field == "COUNT" then
        if let some w := v then vs := w :: vs
        v := some {}
      else
        let some w := v | throw s!"{field} before COUNT"
        match field with
        | "n" => v := some { w with n := ← hexNat value }
        | "e" => v := some { w with e := ← hexNat value }
        | "d" => v := some { w with d := ← hexNat value }
        | "c" => v := some { w with c := ← hexNat value }
        | "k" => v := some { w with k := ← hexNat value }
        | "Result" => v := some { w with pass := value == "Pass" }
        | "c^d" | "k^e" => pure ()
        | _ => throw s!"unknown field {field}"
    | _ => pure ()
  if let some w := v then vs := w :: vs
  return vs.reverse

/-- `x` as octets, most significant first, with no leading zero. -/
def bytes (x : Nat) : List Byte := i2osp x ((Nat.log2 x) / 8 + 1)

/-- Checks one vector; returns the number of candidates the factor recovery
tried. -/
def check (v : Vector) : Except String Nat := do
  let n := v.n
  let e := v.e
  let d := v.d
  let nB := bytes n
  let len := nB.length
  unless len * 8 == Nat.log2 n + 1 do throw "modulus not a whole number of octets"
  let eB := bytes e
  let dB := bytes d
  let cB := i2osp v.c len
  let kB := i2osp v.k len
  unless modulusValid n len do throw "modulus rejected"
  let expected : Option (List Byte) := if v.pass then some kB else none
  if v.pass then
    unless v.k < n do throw "result not below n"
    unless publicOp nB eB kB == some cB do throw "RSAEP mismatch"
  else
    unless v.c ≥ n && v.c < 256 ^ len do throw "failing vector's input not in [n, 256^k)"
    unless publicOp nB eB cB == none do throw "RSAEP accepted an input not below n"
  let (res, tries) := privateExponents nB eB cB dB
  unless res == expected do throw "privateExponents mismatch"
  unless 1 ≤ tries && tries ≤ recoverTries do throw s!"{tries} tries"
  let (some (p, q), tries') := recoverPrimes n e d | throw "factors not found"
  unless tries' == tries do throw "tries mismatch"
  -- The `i`-th candidate is `g = i + 1`: those before the last tried fail.
  let (t, r) := splitTwos (d * e - 1)
  unless (List.range tries).all (fun i => (recoverStep n t r (i + 2)).isSome == (i + 1 == tries)) do
    throw "candidates tried"
  -- The input `n` itself is not below `n`.
  unless publicOp nB eB nB == none && (privateExponents nB eB nB dB).1 == none do
    throw "accepted the input n"
  unless p * q == n && p > q && q > 1 do throw "factors wrong"
  unless privatePrimes nB cB (bytes p) (bytes q) dB == expected do
    throw "privatePrimes mismatch"
  let some (dP, dQ, qInv) := crtValues p q d | throw "no CRT values"
  unless (q * qInv) % p == 1 && dP < p - 1 && dQ < q - 1 do throw "CRT values wrong"
  let pLen := (bytes p).length
  let qLen := (bytes q).length
  unless privateCrt nB cB (bytes p) (bytes q) (i2osp dP pLen) (i2osp dQ qLen)
      (i2osp qInv pLen) == expected do
    throw "privateCrt mismatch"
  unless privateCrt nB cB (i2osp p (pLen + 1)) (bytes q) (i2osp dP (pLen + 1))
      (i2osp dQ qLen) (i2osp qInv (pLen + 1)) == expected do
    throw "privateCrt mismatch with unbalanced lengths"
  unless privateCrt nB cB (i2osp p (pLen + 1)) (bytes q) (i2osp dP (pLen + 1))
      (i2osp dQ qLen) (i2osp (qInv + p) (pLen + 1)) == none do
    throw "privateCrt accepted qInv ≥ p"
  unless privateCrt nB cB (bytes p) (i2osp (q + 2) qLen) (i2osp dP pLen) (i2osp dQ qLen)
      (i2osp qInv pLen) == none do
    throw "privateCrt accepted p q ≠ n"
  unless privatePrimes nB cB (bytes p) (i2osp (q + 2) qLen) dB == none do
    throw "privatePrimes accepted p q ≠ n"
  -- A modulus with a leading zero octet, or an even one, is not valid.
  unless publicOp (0 :: nB) eB (0 :: kB) == none do throw "accepted a leading zero"
  unless publicOp (i2osp (n + 1) len) eB kB == none do throw "accepted an even modulus"
  unless (privateExponents (i2osp (n + 1) len) eB cB dB) == (none, 0) do
    throw "privateExponents accepted an even modulus"
  return tries

/-- Edges on arithmetic inputs. -/
def checkEdges : Except String Unit := do
  for (n, k, ok) in [(2 ^ 511 + 1, 64, true), (2 ^ 511 - 1, 64, false), (2 ^ 512 - 1, 64, true),
      (2 ^ 512 - 2, 64, false), (2 ^ 8192 - 1, 1024, true), (2 ^ 8192 + 1, 1025, false),
      (2 ^ 520 + 1, 66, true), (2 ^ 520 + 1, 67, false)] do
    unless modulusValid n k == ok do
      throw s!"modulusValid of a {k}-octet modulus"
  for x in List.range 70000 do
    unless os2ip (i2osp x 3) == x % 2 ^ 24 do throw "I2OSP/OS2IP"
  for m in List.range 120 do
    if m < 2 then continue
    for a in List.range (2 * m) do
      let brute := (List.range m).find? fun x => a * x % m == 1
      unless inverse a m == brute do throw s!"inverse {a} mod {m}"
  -- `d e - 1` odd, or `d e < 2`: no factors, and no candidate tried.
  unless recoverPrimes (2 ^ 511 + 1) 3 2 == (none, 0) do throw "odd de - 1"
  unless recoverPrimes (2 ^ 511 + 1) 3 0 == (none, 0) do throw "zero d"
  unless recoverPrimes (2 ^ 511 + 1) 1 1 == (none, 0) do throw "de = 1"

#assert_standard_axioms Spec.Rsa.publicOp
#assert_standard_axioms Spec.Rsa.privateCrt
#assert_standard_axioms Spec.Rsa.privatePrimes
#assert_standard_axioms Spec.Rsa.privateExponents
#assert_no_compiler_overrides Spec.Rsa.publicOp Spec.Rsa.privateCrt Spec.Rsa.privatePrimes Spec.Rsa.privateExponents
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "RSA edges: {e}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-rsadp" / "RSADPComponent800_56B.txt")
  let result : Except String Unit := do
    let vs ← parse text
    unless vs.length == 60 do throw s!"unexpected vector count {vs.length}"
    unless (vs.filter (·.pass)).length == 40 do throw "unexpected passing vector count"
    for (v, i) in vs.zipIdx do
      match check v with
      | .ok _ => pure ()
      | .error e => throw s!"vector {i} ({Nat.log2 v.n + 1} bits): {e}"
  match result with
  | .ok () => pure ()
  | .error e => throwError "RSADPComponent800_56B.txt: {e}"

end VG.Test.Rsa
