import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Aes

/-!
# Known-answer tests for the AES specification

The NIST CAVP AES known-answer tests for ECB (`GFSbox`, `KeySbox`, `VarKey`
and `VarTxt`, each for 128-, 192- and 256-bit keys), read from the vendored
response files under `vectors/nist-cavp/aes/` (see `vectors/sources/`)
when this file is built and checked against `VG.Spec.Aes.encrypt` (the
`ENCRYPT` vectors) and `VG.Spec.Aes.decrypt` (the `DECRYPT` vectors), so
that a transcription error in the spec fails the build. Every `GFSbox` and
`KeySbox` vector is checked, and the first two `VarKey` and `VarTxt`
vectors of each file, in each direction. (Evaluating the spec is slow; the Rust tests run the full
Wycheproof suite against the implementation.)
-/

namespace VG.Test.Aes

open Lean Elab Command

/-- One record of a CAVP response file: the bracketed parameters of the
section it is in (e.g. `ENCRYPT`, or `IVlen = 96`), its `name = value`
fields, and whether it has a bare `FAIL` line. -/
structure Record where
  params : List (String × String)
  fields : List (String × String) := []
  fail : Bool := false

def Record.get (r : Record) (name : String) : Except String String :=
  match r.fields.find? (·.1 == name) with
  | some (_, v) => pure v
  | none => throw s!"no `{name}`"

def Record.bytes (r : Record) (name : String) : Except String (List Byte) := do
  let v ← r.get name
  match Sha256.unhex v with
  | some bs => pure bs
  | none => throw s!"`{name} = {v}` is not hex"

/-- The records of a CAVP response file. A record starts at a `COUNT` or
`Count` field; bracketed lines set the parameters of the records that
follow (`[ENCRYPT]` a flag, `[IVlen = 96]` a value), and a new run of
bracketed lines starts a new section. -/
def records (text : String) : List Record := Id.run do
  let mut out : Array Record := #[]
  let mut params : List (String × String) := []
  let mut inHeader := false
  let mut cur : Option Record := none
  for l in text.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    if l.startsWith "[" then
      if let some r := cur then out := out.push r
      cur := none
      unless inHeader do params := []
      inHeader := true
      let inner := (l.drop 1).takeWhile (· != ']') |>.toString
      match inner.splitOn " = " with
      | [k, v] => params := params ++ [(k, v)]
      | _ => params := params ++ [(inner, "")]
      continue
    inHeader := false
    if l == "FAIL" then
      cur := cur.map ({ · with fail := true })
      continue
    match l.splitOn " = " with
    | [k, v] =>
      if k == "COUNT" || k == "Count" then
        if let some r := cur then out := out.push r
        cur := some { params }
      cur := cur.map fun r => { r with fields := r.fields ++ [(k, v)] }
    | _ => match l.splitOn " =" with
      | [k, ""] => cur := cur.map fun r => { r with fields := r.fields ++ [(k, "")] }
      | _ => pure ()
  if let some r := cur then out := out.push r
  return out.toList

/-- The contents of `vectors/nist-cavp/<dir>/<name>`. -/
def readVectors (dir name : String) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / "nist-cavp" / dir / name)

run_cmd do
  let mut n : Nat := 0
  for kind in ["GFSbox", "KeySbox", "VarKey", "VarTxt"] do
    for bits in [128, 192, 256] do
      let name := s!"ECB{kind}{bits}.rsp"
      for dir in ["ENCRYPT", "DECRYPT"] do
        let rs := (records (← readVectors "aes" name)).filter (·.params.any (·.1 == dir))
        if rs.isEmpty then throwError "{name}: no {dir} vectors"
        let rs := if kind == "VarKey" || kind == "VarTxt" then rs.take 2 else rs
        for r in rs do
          let v : Except String _ := do
            pure (← r.bytes "KEY", ← r.bytes "PLAINTEXT", ← r.bytes "CIPHERTEXT")
          match v with
          | .error e => throwError "{name}: {e}"
          | .ok (key, pt, ct) =>
            unless key.length == bits / 8 do throwError "{name}: a {key.length}-byte key"
            if dir == "ENCRYPT" then
              unless Spec.Aes.encrypt key pt == ct do
                throwError "{name}, COUNT = {(r.get "COUNT").toOption}: AES encryption is wrong"
            else
              unless Spec.Aes.decrypt key ct == pt do
                throwError "{name}, COUNT = {(r.get "COUNT").toOption}: AES decryption is wrong"
            n := n + 1
  unless n == 182 do throwError "expected 182 vectors, checked {n}"

-- The inverse S-box inverts the S-box, on every byte.
run_cmd do
  for x in List.range 256 do
    let b : Byte := BitVec.ofNat 8 x
    unless Spec.Aes.invSbox (Spec.Aes.sbox b) == b do throwError "invSbox (sbox {x}) ≠ {x}"

end VG.Test.Aes
