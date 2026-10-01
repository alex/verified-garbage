import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Cmac

/-!
# Known-answer tests for the CMAC specification

Read from the unmodified published files under `vectors/` (provenance in
`vectors/sources/`) when this file is built and checked against
`VG.Spec.Cmac`, so that a transcription error in the spec fails the build:

* RFC 4493 §4: the subkey generation (`L`, `K1` and `K2`, checking
  `VG.Spec.Cmac.subkeys`) and all four AES-128-CMAC examples (messages of
  0, 16, 40 and 64 bytes: the empty message, complete and partial last
  blocks).
* NIST CAVP CMAC generation, for 128-, 192- and 256-bit keys: the first
  vector of every message and MAC length, but the 65536-byte messages
  (evaluating the spec is slow; the Rust tests run the full Wycheproof suite
  against the implementation). These cover empty messages, complete and
  partial last blocks, and MACs of 4 to 16 bytes.
* NIST CAVP CMAC verification, for 128- and 256-bit keys: the first two
  vectors of every message and MAC length, checking `VG.Spec.Cmac.verify`;
  they include both outcomes.
-/

namespace VG.Test.Cmac

open Lean Elab Command Test.Aes

/-- The fields of RFC 4493 §4: each line `label hex hex …`, and the hex
groups of the indented lines that continue it. `M <empty string>` is the
empty message. -/
def rfcFields (text : String) : List (String × List Byte) := Id.run do
  let excerpt := (((text.splitOn "4.  Test Vectors").drop 1).headD "").splitOn "5.  Acknowledgement"
  let mut out : Array (String × String) := #[]
  for l in (excerpt.headD "").splitOn "\n" do
    let l := l.trimAsciiEnd.toString
    let words := (l.splitOn " ").filter (· ≠ "")
    let isHex (w : String) := w.length == 8 && w.all Char.isHexDigit
    if l.startsWith "   " && !(l.startsWith "    ") then
      match words with
      | label :: rest =>
        if l.endsWith "<empty string>" then out := out.push (label, "")
        else if !rest.isEmpty && rest.all isHex then out := out.push (label, String.join rest)
      | [] => pure ()
    else if !words.isEmpty && words.all isHex && !out.isEmpty then
      out := out.modify (out.size - 1) fun (k, v) => (k, v ++ String.join words)
  return out.toList.filterMap fun (k, v) => (Sha256.unhex v).map (k, ·)

/-- The message of a CAVP record: `Msg`, or nothing if `Mlen` is 0 (the files
write `Msg = 00` for the empty message). -/
def message (r : Record) : Except String (List Byte) := do
  if (← r.get "Mlen") == "0" then pure [] else r.bytes "Msg"

/-- The first `k` records with each `Mlen` and `Tlen` that `p` selects. -/
def firstOfLengths (k : Nat) (p : Record → Bool) (rs : List Record) : List Record := Id.run do
  let mut seen : List ((String × String) × Nat) := []
  let mut out : Array Record := #[]
  for r in rs do
    let key := ((r.get "Mlen").toOption.getD "", (r.get "Tlen").toOption.getD "")
    let n := (seen.lookup key).getD 0
    if p r && n < k then
      out := out.push r
      seen := (key, n + 1) :: seen.filter (·.1 != key)
  return out.toList

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

run_cmd do
  let fields := rfcFields (← readFile ("rfc4493" / "rfc4493.txt"))
  let get (k : String) : CommandElabM (List Byte) := match fields.lookup k with
    | some v => pure v
    | none => throwError "RFC 4493: no `{k}`"
  let key ← get "K"
  unless key.length == 16 do throwError "RFC 4493: a {key.length}-byte key"
  unless Spec.Aes.encrypt key (Spec.Cmac.zeros 16) == (← get "AES-128(key,0)") do
    throwError "RFC 4493: L = CIPH_K(0) is wrong"
  unless Spec.Cmac.subkeys (Spec.Cmac.aes key) 16 == (← get "K1", ← get "K2") do
    throwError "RFC 4493: the subkeys are wrong"
  let msgs := fields.filter (·.1 == "M") |>.map (·.2)
  let macs := fields.filter (·.1 == "AES-CMAC") |>.map (·.2)
  unless msgs.map List.length == [0, 16, 40, 64] && macs.length == 4 do
    throwError "RFC 4493: expected 4 examples, got messages of {msgs.map List.length} bytes"
  for (msg, t) in msgs.zip macs do
    unless Spec.Cmac.aesCmac key 16 msg == t do
      throwError "RFC 4493: the AES-CMAC of {msg.length} bytes is wrong"

run_cmd do
  let mut n : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"CMACGenAES{bits}.rsp"
    let rs := records (← readVectors "cmac-aes" name)
    for r in firstOfLengths 1 (fun r => (r.get "Mlen").toOption != some "65536") rs do
      let v : Except String _ := do pure (← r.bytes "Key", ← message r, ← r.bytes "Mac")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok (key, msg, t) =>
        unless key.length == bits / 8 do throwError "{name}: a {key.length}-byte key"
        unless Spec.Cmac.aesCmac key t.length msg == t do
          throwError "{name}, Count = {(r.get "Count").toOption}: CMAC generation is wrong"
        n := n + 1
  unless n == 38 do throwError "expected 38 generation vectors, checked {n}"

run_cmd do
  let mut pass : Nat := 0
  let mut fail : Nat := 0
  for bits in [128, 256] do
    let name := s!"CMACVerAES{bits}.rsp"
    for r in firstOfLengths 2 (fun _ => true) (records (← readVectors "cmac-aes" name)) do
      let v : Except String _ := do
        pure (← r.bytes "Key", ← message r, ← r.bytes "Mac", ← r.get "Result")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok (key, msg, t, result) =>
        unless key.length == bits / 8 do throwError "{name}: a {key.length}-byte key"
        let valid := result == "P"
        unless valid || result.startsWith "F" do throwError "{name}: `Result = {result}`"
        unless Spec.Cmac.verify (Spec.Cmac.aes key) 16 msg t == valid do
          throwError "{name}, Count = {(r.get "Count").toOption}: CMAC verification is wrong"
        if valid then pass := pass + 1 else fail := fail + 1
  unless pass + fail == 44 && pass > 0 && fail > 0 do
    throwError "expected 44 verification vectors of both outcomes, checked {pass} valid and {fail} not"

end VG.Test.Cmac
