import Lean.Elab.Command
import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! # DSA specification regression tests
Known answers are parsed from the byte-for-byte NIST CAVP files, including
published nonces for signing. No vector values are embedded in this test.
Primality is not recomputed: CAVP supplies the validated domain parameters.
-/
namespace VG.Test.Dsa
open Lean Elab Command Spec.Dsa

def hex (s : String) : Except String (List Byte) := do
  let cs := s.toList
  if cs.length % 2 != 0 then throw "odd hex length"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw "invalid hex digit"
  let rec loop : List Char → Except String (List Byte)
    | [] => pure []
    | h :: l :: rest => do return BitVec.ofNat 8 (16 * (← digit h) + (← digit l)) :: (← loop rest)
    | _ => throw "odd hex length"
  loop cs

structure Vector where
  params : Params := ⟨0, 0, 0⟩
  hash : String := ""
  msg : List Byte := []
  x : Nat := 0
  y : Nat := 0
  k : Nat := 0
  sig : Signature := ⟨0, 0⟩
  pass : Bool := true

def parse (text : String) (signing : Bool) : Except String (List Vector) := do
  let mut v : Vector := {}
  let mut vs := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "[mod = " then
      let some h := (line.splitOn ", ").getLast? | throw "missing hash header"
      v := { v with hash := h.replace "]" "" }
    else
      match line.splitOn " = " with
      | [field, value] =>
        if field == "Result" then
          v := { v with pass := value.startsWith "P" }
          vs := v :: vs
        else
          let bytes ← hex value
          let n := decodeBE bytes
          match field with
          | "P" => v := { v with params := { v.params with p := n } }
          | "Q" => v := { v with params := { v.params with q := n } }
          | "G" => v := { v with params := { v.params with g := n } }
          | "Msg" => v := { v with msg := bytes }
          | "X" => v := { v with x := n }
          | "Y" => v := { v with y := n }
          | "K" => v := { v with k := n }
          | "R" => v := { v with sig := { v.sig with r := n } }
          | "S" =>
            v := { v with sig := { v.sig with s := n } }
            if signing then vs := v :: vs
          | _ => throw s!"unknown field {field}"
      | _ => pure ()
  return vs.reverse

def digest (v : Vector) : Except String (List Byte) :=
  match v.hash with
  | "SHA-1" => pure (Spec.Sha1.hash v.msg)
  | "SHA-224" => pure (Spec.Sha256.sha224 v.msg)
  | "SHA-256" => pure (Spec.Sha256.hash v.msg)
  | "SHA-384" => pure (Spec.Sha512.sha384 v.msg)
  | "SHA-512" => pure (Spec.Sha512.sha512 v.msg)
  | h => throw s!"unknown hash {h}"

def check (v : Vector) (signing : Bool) : Except String Unit := do
  let d ← digest v
  let key : Key := ⟨v.params, v.y, some v.x⟩
  unless verify key v.sig d == v.pass do throw "verification mismatch"
  if signing then
    unless signWithNonce key d v.k == some v.sig do throw "signature mismatch"
    unless sign key d [0, v.params.q, v.k] == some v.sig do throw "nonce rejection failed"
    unless generate v.params [0, v.params.q, v.x] == some key do throw "key generation mismatch"
    unless toComponents key == (v.params.p, v.params.q, v.params.g, v.y, some v.x) do
      throw "component export mismatch"
    unless signWithNonce { key with x := none } d v.k == none do throw "signed with public key"
    unless signWithNonce { key with x := some (v.x + 1) } d v.k == none do
      throw "accepted inconsistent private key"
    for bad in [⟨0, v.sig.s⟩, ⟨v.params.q, v.sig.s⟩, ⟨v.sig.r, 0⟩, ⟨v.sig.r, v.params.q⟩] do
      if verify key bad d then throw "accepted out-of-range signature"
    if verify { key with y := 1 } v.sig d then throw "accepted identity public key"
    -- Truncation discards low digest bits; extending a long digest by a
    -- byte must not change z. An empty digest represents zero.
    unless digestScalar v.params.q (d ++ [0]) == digestScalar v.params.q d ||
      8 * d.length < bitLength v.params.q do throw "digest truncation mismatch"
    unless digestScalar v.params.q [] == 0 do throw "empty digest mismatch"

/-- Check published A.1.1.2 prime candidates without rerunning primality.
The CAVP archive also contains constructions outside this spec; only the
three default size/hash combinations are selected here. -/
def checkParameterCandidates (text : String) : Except String Unit := do
  let mut hash := ""
  let mut p := 0
  let mut q := 0
  let mut seed := []
  let mut checked := 0
  for raw in (text.splitOn "\n").takeWhile (!·.startsWith "[A.1.2") do
    if raw.startsWith "\t" then continue
    let line := raw.trimAscii.toString
    if line.startsWith "[mod = " then
      let some h := (line.splitOn ", ").getLast? | throw "missing parameter hash"
      hash := h.replace "]" ""
    else
      match line.splitOn " = " with
      | ["P", value] => p := decodeBE (← hex value)
      | ["Q", value] => q := decodeBE (← hex value)
      | ["domain_parameter_seed", value] => seed := ← hex value
      | ["counter", value] =>
        let some counter := value.toNat? | throw "invalid counter"
        let l := bitLength p
        let n := bitLength q
        if (l == 1024 && n == 160 && hash == "SHA-1") ||
            ((l == 2048 || l == 3072) && n == 256 && hash == "SHA-256") then
          unless qCandidate n seed == q do throw "q candidate mismatch"
          unless pCandidate l n q seed (1 + counter * ((l - 1) / n + 1)) == p do
            throw "p candidate mismatch"
          checked := checked + 1
      | _ => pure ()
  unless checked == 15 do throw s!"unexpected parameter candidate count {checked}"

/-- Synthetic small-group properties test the rare zero-component retry
paths. These are arithmetic inputs, not cryptographic known-answer vectors;
production imports reject their unsupported bit lengths. -/
def checkEdges : Except String Unit := do
  let a : Params := ⟨11, 5, powMod 2 2 11⟩
  let mut retries := 0
  let mut successes := 0
  for x in List.range a.q do
    if x == 0 then continue
    let some key := generate a [x] | throw "small-group key generation failed"
    for k in List.range a.q do
      if k == 0 then continue
      for z in List.range 8 do
        let d := [BitVec.ofNat 8 (z * 32)]
        match signWithNonce key d k with
        | none => retries := retries + 1
        | some sig =>
          successes := successes + 1
          unless verify key sig d do throw "small-group signature did not verify"
  unless retries > 0 && successes > 0 do throw "zero-component retry path not exercised"
  unless fromComponents a.p a.q a.g 4 (some 1) == none do
    throw "import accepted unsupported parameter sizes"
  unless sampleScalar a.q [0, a.q, a.q + 1] == none do throw "invalid scalar accepted"
  unless generate a [] == none do throw "empty randomness tape accepted"
  for bits in [0, 512, 1024, 2048, 3072, 4096] do
    unless generateParameters bits [] [] == none do throw "empty seed tape accepted"
  for n in List.range 4 do
    for x in List.range 512 do
      unless decodeBE (encodeBE n x) == x % 2 ^ (8 * n) do throw "big-endian wrap failed"

#assert_standard_axioms Spec.Dsa.generateParameters
#assert_standard_axioms Spec.Dsa.fromComponents
#assert_standard_axioms Spec.Dsa.sign
#assert_standard_axioms Spec.Dsa.verify
#assert_no_compiler_overrides Spec.Dsa.generateParameters Spec.Dsa.fromComponents Spec.Dsa.sign Spec.Dsa.verify
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "DSA edges: {e}"
  let params ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "PQGGen.txt")
  match checkParameterCandidates params with
  | .ok () => pure ()
  | .error e => throwError "PQGGen.txt: {e}"
  for (name, signing) in [("SigGen.txt", true), ("SigVer.rsp", false)] do
    let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / name)
    let result := do
      let vs ← parse text signing
      unless vs.length == 300 do throw s!"unexpected vector count {vs.length}"
      for (v, i) in vs.zipIdx do
        match check v signing with
        | .ok () => pure ()
        | .error e => throw s!"vector {i}, {v.hash}, L={bitLength v.params.p}: {e}"
    match result with
    | .ok () => pure ()
    | .error e => throwError "{name}: {e}"

end VG.Test.Dsa
