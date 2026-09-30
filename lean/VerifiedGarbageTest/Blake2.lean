import Lean.Data.Json
import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Blake2

/-!
# Known-answer tests for the BLAKE2b and BLAKE2s specification

Read when this file is built and checked against `VG.Spec.Blake2`, so that a
transcription error in the spec fails the build:

* the examples of RFC 7693, BLAKE2b-512 and BLAKE2s-256 of `"abc"`
  (Appendices A and B), read from the vendored `vectors/rfc7693/rfc7693.txt`;
* the RFC's self-test (Appendix E), which hashes pseudorandom messages of
  six lengths with four digest lengths, unkeyed and keyed, and compares the
  hash of all those digests with the one given; its parameters and expected
  results are read from the RFC's C source;
* every BLAKE2b and BLAKE2s vector of the reference implementation's
  known-answer tests, `vectors/blake2-kat/blake2-kat.json`: messages of 0 to
  255 bytes, unkeyed and with a key of the maximum length, and the maximum
  digest length.

(See `vectors/sources/`.) Each digest is computed both as the RFC defines it
(`blake2`) and as the streaming functions do (`finalHash` from `init` of
`keyBlock key ++ m`), so the vectors check the definitions the contracts are
stated in too.
-/

namespace VG.Test.Blake2

open Lean Elab Command Spec.Blake2

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The digest of `m` with key `key`, both as `blake2` and as `finalHash`
computes it, if they agree. -/
def digest {w : Nat} (P : Params w) (nn : Nat) (key m : List Byte) : Except String (List Byte) := do
  let md := blake2 P nn key m
  unless (finalHash P (init P nn key.length) (keyBlock w key ++ m)).take nn == md do
    throw s!"blake2 and finalHash disagree on a {m.length}-byte message and {key.length}-byte key"
  return md

/-- The bytes of the lines after the one starting with `head` (up to a blank
line), written as hex pairs separated by spaces, the first line after `=`. -/
def example_ (lines : List String) (head : String) : Except String (List Byte) := do
  let some i := lines.findIdx? (·.trimAscii.toString.startsWith head)
    | throw s!"no `{head}` line"
  let block := (lines.drop i).takeWhile (!·.trimAscii.isEmpty)
  let some (_ :: rest) := block.head?.map (·.splitOn "=")
    | throw s!"expected `{head} = ...`"
  let hex := String.join ((String.intercalate "=" rest :: block.tail).map fun l =>
    String.join ((l.splitOn " ").map (·.trimAscii.toString)))
  let some bytes := Sha256.unhex hex.toLower | throw s!"expected hex bytes after `{head}`"
  return bytes

/-- The numbers of the C array initializer `name[...] = { ... };` in `text`
(`0x` hex or decimal). -/
def cArray (text : String) (name : String) : Except String (List Nat) := do
  let _ :: after :: _ := text.splitOn s!"{name}[" | throw s!"no array `{name}`"
  let _ :: body :: _ := after.splitOn "{" | throw s!"no initializer for `{name}`"
  let body :: _ := body.splitOn "}" | throw s!"unterminated initializer for `{name}`"
  (body.splitOn ",").mapM fun e => do
    let e := e.trimAscii.toString
    let n := if e.startsWith "0x" || e.startsWith "0X" then
        (Sha256.unhex (e.drop 2).toString.toLower).map fun bs =>
          bs.foldl (fun acc b => 256 * acc + b.toNat) 0
      else e.toNat?
    match n with
    | some n => pure n
    | none => throw s!"`{name}`: expected a number, got {e}"

/-- `selftest_seq(out, len, seed)` of Appendix E: `len` bytes of a Fibonacci
generator seeded with `seed`. -/
def selftestSeq (len seed : Nat) : List Byte :=
  let rec go : Nat → BitVec 32 → BitVec 32 → List Byte
    | 0, _, _ => []
    | n + 1, a, b => let t := a + b; t.extractLsb' 24 8 :: go n b t
  go len (0xDEAD4BAD * BitVec.ofNat 32 seed) 1

/-- `blake2b_selftest()` or `blake2s_selftest()` of Appendix E: the 32-byte
unkeyed hash of the digests, unkeyed and keyed with `selftest_seq(key,
outlen, outlen)`, of `selftest_seq(in, inlen, inlen)` for each `outlen` in
`mdLens` and `inlen` in `inLens`. -/
def selftest {w : Nat} (P : Params w) (mdLens inLens : List Nat) : Except String (List Byte) := do
  let mut mds : List Byte := []
  for outlen in mdLens do
    for inlen in inLens do
      let m := selftestSeq inlen inlen
      mds := mds ++ (← digest P outlen [] m)
      mds := mds ++ (← digest P outlen (selftestSeq outlen outlen) m)
  digest P 32 [] mds

/-- Checks the vectors of RFC 7693. -/
def checkRfc (text : String) : Except String Unit := do
  let lines := text.splitOn "\n"
  let abc := ascii "abc"
  unless (← digest b 64 [] abc) == (← example_ lines "BLAKE2b-512(\"abc\")") do
    throw "BLAKE2b-512(\"abc\") of Appendix A is wrong"
  unless (← digest s 32 [] abc) == (← example_ lines "BLAKE2s-256(\"abc\")") do
    throw "BLAKE2s-256(\"abc\") of Appendix B is wrong"
  let res ← cArray text "blake2b_res"
  unless res.length == 32 do throw "expected 32 bytes of blake2b_res"
  unless (← selftest b (← cArray text "b2b_md_len") (← cArray text "b2b_in_len")) ==
      res.map (BitVec.ofNat 8) do
    throw "blake2b_selftest() of Appendix E fails"
  let res ← cArray text "blake2s_res"
  unless res.length == 32 do throw "expected 32 bytes of blake2s_res"
  unless (← selftest s (← cArray text "b2s_md_len") (← cArray text "b2s_in_len")) ==
      res.map (BitVec.ofNat 8) do
    throw "blake2s_selftest() of Appendix E fails"

/-- Checks the BLAKE2b and BLAKE2s vectors of `blake2-kat.json`, returning how
many there were of each. -/
def checkKat (j : Json) : Except String (Nat × Nat) := do
  let vs ← j.getArr?
  let mut nb := 0
  let mut ns := 0
  for v in vs do
    let hash ← v.getObjValAs? String "hash"
    let field (k : String) : Except String (List Byte) := do
      let some bs := Sha256.unhex (← v.getObjValAs? String k) | throw s!"`{k}` is not hex"
      return bs
    let (m, key, out) := (← field "in", ← field "key", ← field "out")
    if hash == "blake2b" then
      unless (← digest b out.length key m) == out do
        throw s!"BLAKE2b of the {m.length}-byte message with a {key.length}-byte key is wrong"
      nb := nb + 1
    else if hash == "blake2s" then
      unless (← digest s out.length key m) == out do
        throw s!"BLAKE2s of the {m.length}-byte message with a {key.length}-byte key is wrong"
      ns := ns + 1
  return (nb, ns)

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Blake2.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7693" / "rfc7693.txt")
  if let .error e := checkRfc text then throwError "rfc7693.txt: {e}"
  let json ← IO.FS.readFile (root / "vectors" / "blake2-kat" / "blake2-kat.json")
  let j ← match Json.parse json with
    | .ok j => pure j
    | .error e => throwError "blake2-kat.json: {e}"
  match checkKat j with
  | .error e => throwError "blake2-kat.json: {e}"
  | .ok (nb, ns) =>
    unless nb == 512 && ns == 512 do
      throwError "expected 512 BLAKE2b and 512 BLAKE2s vectors, got {nb} and {ns}"

end VG.Test.Blake2
