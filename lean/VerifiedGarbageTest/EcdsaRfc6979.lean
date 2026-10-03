import Lean.Elab.Command
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# Deterministic ECDSA (RFC 6979) specification tests

From the byte-for-byte vendored RFC:

* The detailed example of §A.1.2 (the curve K-163, whose order `q` has 163
  bits, and HMAC-SHA-256): `int2octets(x)`, `bits2octets(h1)`, `K` and `V`
  after steps b to g, and the three candidates `T` and `k`, the first two
  rejected (above `q - 1`), with `K` and `V` after each rejection. Only `q`
  of K-163 matters to the generation of `k`; the rest of the curve here is
  a placeholder.
* The ten signatures of §A.2.5 (P-256; "sample" and "test" with SHA-1,
  SHA-224, SHA-256, SHA-384 and SHA-512): the first candidate is the `k`
  the RFC lists, `sign` gives the listed `(r, s)` after one candidate, and
  the contracts' instances (`P256Sha256.inst`, `P256Sha384.inst`) agree for
  SHA-256 and SHA-384.
-/

namespace VG.Test.EcdsaRfc6979

open Lean Elab Command Spec.Weierstrass Spec.Ecdsa Spec.Ecdsa.Rfc6979

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (fun acc c => match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"invalid hexadecimal digit {c}") 0

def trim (line : String) : String := String.ofList (line.toList.dropWhile (· == ' '))

/-- `name = HEX` (or `name = 0xHEX`) on a line of its own, indented. -/
def field (name : String) (line : String) : Option String :=
  let t := trim line
  if t.startsWith (name ++ " = ") then
    let v := String.ofList (t.toList.drop (name.length + 3))
    some (if v.startsWith "0x" then String.ofList (v.toList.drop 2) else v)
  else none

def one (lines : List String) (name : String) : Except String Nat := do
  match lines.filterMap (field name) with
  | [v] => hexNat v
  | vs => throw s!"expected one {name}, got {vs.length}"

/-- The octets listed under the line `label`: the following lines of
space-separated pairs of hexadecimal digits. -/
def octets (lines : List String) (label : String) : Except String (List Byte) := do
  let rest := (lines.dropWhile (trim · != label)).drop 1
  if rest.isEmpty then throw s!"no {label}"
  let rows := rest.takeWhile fun l =>
    let ws := (trim l).splitOn " " |>.filter (· ≠ "")
    !ws.isEmpty && ws.all (·.length == 2)
  let ws := rows.flatMap fun l => (trim l).splitOn " " |>.filter (· ≠ "")
  if ws.isEmpty then throw s!"no octets under {label}"
  ws.mapM fun w => do return BitVec.ofNat 8 (← hexNat w)

def sectionOf (text start stop : String) : List String :=
  (((text.splitOn "\n").dropWhile (!·.startsWith start)).drop 1).takeWhile (!·.startsWith stop)

def utf8 (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- K-163's order `q`, and a placeholder for the rest of the curve. -/
def k163 (q : Nat) (h : q ≠ 0) : Curve :=
  @Curve.mk 2 0 0 0 0 q 21 ⟨by decide⟩ ⟨h⟩

def H := Spec.Hmac.sha256

/-- §A.1.2. -/
def checkDetailed (text : String) : Except String Unit := do
  let keys := sectionOf text "A.1.1.  Key Pair" "A.1.2."
  let q ← one keys "q"
  let x ← one keys "x"
  let lines := sectionOf text "A.1.2.  Generation of k" "A.1.3."
  if h : q = 0 then throw "q = 0" else
  let C := k163 q h
  unless nBits C == 163 do throw s!"qlen = {nBits C}"
  let h1 ← octets lines "h1"
  unless Spec.Sha256.hash (utf8 "sample") == h1 do throw "h1"
  unless int2octets C x == (← octets lines "int2octets(x)") do throw "int2octets(x)"
  unless bits2octets C h1 == (← octets lines "bits2octets(h1)") do throw "bits2octets(h1)"
  let (K, V) := init C H 32 x h1
  unless K == (← octets lines "K after step f:") do throw "K after step f"
  unless V == (← octets lines "V after step g:") do throw "V after step g"
  unless blocks C 32 == 1 do throw "blocks"
  -- The first two candidates are above `q - 1`; the third is suitable.
  let (T, V) := genT H K 1 V
  unless T == (← octets lines "T (first try)") do throw "T (first try)"
  let k1 := bits2int C T
  unless k1 == 0x4982D236F3FFC758838CA6F5E9FEA455106AF3B2B && q ≤ k1 do throw "k1"
  let (K, V) := next H K V
  unless K == (← octets lines "new K") && V == (← octets lines "new V") do throw "new K, V"
  let (T, V) := genT H K 1 V
  unless T == (← octets lines "T (second try)") do throw "T (second try)"
  let k2 := bits2int C T
  unless k2 == 0x63863C30451DADF4944DF4877B740D4F160A8B6AB && q ≤ k2 do throw "k2"
  let (K, V) := next H K V
  unless K == (← octets lines "new K (2)") && V == (← octets lines "new V (2)") do
    throw "new K (2), V (2)"
  let (T, _) := genT H K 1 V
  unless T == (← octets lines "T (third try)") do throw "T (third try)"
  let k3 := bits2int C T
  unless k3 == (← one lines "k") && k3 < q do throw "k3"

structure Vector where
  hash : String
  message : String
  k : Nat
  r : Nat
  s : Nat

/-- Each hash function of §A.2.5: its HMAC hash function and output length. -/
def hashes : List (String × Spec.Hmac.HashFunction × Nat) :=
  [("SHA-1", Spec.Hmac.sha1, 20), ("SHA-224", Spec.Hmac.sha224, 28),
    ("SHA-256", Spec.Hmac.sha256, 32), ("SHA-384", Spec.Hmac.sha384, 48),
    ("SHA-512", Spec.Hmac.sha512, 64)]

/-- The private key and the signatures of §A.2.5. -/
def parse (text : String) : Except String (Nat × List Vector) := do
  let lines := sectionOf text "A.2.5.  ECDSA, 256 Bits" "A.2.6."
  let x ← one lines "x"
  let mut vs : Array Vector := #[]
  let mut header : Option (String × String) := none
  let mut k : Option Nat := none
  let mut r : Option Nat := none
  for line in lines do
    let t := trim line
    if t.startsWith "With " then
      match t.splitOn ", message = \"" with
      | [h, m] => header := some (String.ofList (h.toList.drop 5), (m.splitOn "\"").headD "")
      | _ => throw s!"unexpected line {t}"
    else if let some v := field "k" line then k := some (← hexNat v)
    else if let some v := field "r" line then r := some (← hexNat v)
    else if let some v := field "s" line then
      let (some (h, m), some kv, some rv) := (header, k, r) | throw "incomplete vector"
      vs := vs.push { hash := h, message := m, k := kv, r := rv, s := ← hexNat v }
      header := none; k := none; r := none
  unless vs.size == 10 do throw s!"expected 10 signatures, got {vs.size}"
  return (x, vs.toList)

def C : Curve := Spec.P256.curve

def checkVector (x : Nat) (v : Vector) : Except String Unit := do
  let some (_, H, hlen) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let h1 := H.hash (utf8 v.message)
  unless h1.length == hlen do throw s!"{v.hash}: output length"
  -- The first candidate is the RFC's `k`.
  let (K, V) := init C H hlen x h1
  let (T, _) := genT H K (blocks C hlen) V
  unless bits2int C T == v.k do throw s!"{v.hash}, {v.message}: k mismatch"
  unless sign C H hlen 8 x h1 == (some (v.r, v.s), 1) do
    throw s!"{v.hash}, {v.message}: signature mismatch"
  let insts := [("SHA-256", Spec.Ecdsa.Rfc6979.P256Sha256.inst),
    ("SHA-384", Spec.Ecdsa.Rfc6979.P256Sha384.inst)]
  if let some (_, I) := insts.find? (·.1 == v.hash) then
    unless I.hashLen == hlen && I.ecdsa.curve.n == C.n do throw s!"{v.hash}: instance"
    unless sign I.ecdsa.curve I.hash I.hashLen I.tries x h1 == (some (v.r, v.s), 1) do
      throw s!"{v.hash} instance, {v.message}: signature mismatch"

/-- Keys outside `[1, n-1]` give no signature and no candidate; no
candidate to try gives none. -/
def checkEdges (x : Nat) : Except String Unit := do
  let h1 := Spec.Sha256.hash (utf8 "sample")
  for d in [0, C.n, C.n + 1] do
    unless sign C H 32 8 d h1 == (none, 0) do throw s!"signed with d = {d}"
  unless sign C H 32 0 x h1 == (none, 0) do throw "signed with no candidate"
  unless rlen C == 32 do throw "rlen"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc6979" / "rfc6979.txt")
  let result := do
    checkDetailed text
    let (x, vs) ← parse text
    for v in vs do checkVector x v
    checkEdges x
  match result with
  | .ok () => pure ()
  | .error e => throwError "rfc6979.txt: {e}"

end VG.Test.EcdsaRfc6979
