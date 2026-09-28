import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Pbkdf2

/-!
# Known-answer tests for the PBKDF2 specification

The PBKDF2-HMAC-SHA-256 vectors of Section 11 of RFC 7914, read from the
vendored `vectors/rfc7914/rfc7914.txt` (see `vectors/sources/`) when this
file is built and checked against `VG.Spec.Pbkdf2.pbkdf2HmacSha256`, so that a
transcription error in the spec fails the build. Only the vector with one
iteration is evaluated (the other has 80000, which evaluating the spec
cannot do in reasonable time); its 64-byte key takes two blocks, so it
checks `INT (i)`, the concatenation of the blocks and HMAC-SHA-256 as the
pseudorandom function. The Rust tests run the Wycheproof vectors, with
thousands of iterations, against the implementation.
-/

namespace VG.Test.Pbkdf2

open Lean Elab Command

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- A vector: `PBKDF2-HMAC-SHA-256 (P="…", S="…", c=…, dkLen=…) = …`. -/
structure Vector where
  p : List Byte
  s : List Byte
  c : Nat
  dkLen : Nat
  dk : List Byte

/-- The text between `pre` and the next `post` in `t`. -/
def between (t pre post : String) : Except String String :=
  match t.splitOn pre with
  | [_, rest] => match rest.splitOn post with
    | v :: _ :: _ => pure v
    | _ => throw s!"no `{post}` after `{pre}` in {t}"
  | _ => throw s!"expected one `{pre}` in {t}"

/-- The vectors of Section 11: the paragraphs after its introduction that
start with `PBKDF2-HMAC-SHA-256 (`, up to the next section. -/
def vectors (text : String) : Except String (List Vector) := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  let some start := lines.findIdx? (· == "11.  Test Vectors for PBKDF2 with HMAC-SHA-256")
    | throw "no section 11"
  let sec := (lines.drop (start + 1)).takeWhile (!·.startsWith "12.")
  -- Paragraphs, joined without separators.
  let paras := (sec.splitBy fun a b => !a.isEmpty && !b.isEmpty).map String.join
  let paras := paras.filter (·.startsWith "PBKDF2-HMAC-SHA-256 (")
  paras.mapM fun v => do
    let p ← between v "P=\"" "\""
    let s ← between v "S=\"" "\""
    let some c := (← between v "c=" ",").toNat? | throw s!"bad c in {v}"
    let some dkLen := (← between v "dkLen=" ")").toNat? | throw s!"bad dkLen in {v}"
    let [_, hex] := v.splitOn ") =" | throw s!"no `) =` in {v}"
    let some dk := Sha256.unhex (String.join (hex.splitOn " ")) | throw s!"bad key in {v}"
    return { p := ascii p, s := ascii s, c, dkLen, dk }

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Pbkdf2.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7914" / "rfc7914.txt")
  let vs ← match vectors text with
    | .ok vs => pure vs
    | .error e => throwError "rfc7914.txt: {e}"
  unless vs.map (·.c) == [1, 80000] do throwError "expected vectors with c = 1 and 80000"
  for v in vs.filter (·.c == 1) do
    unless v.dk.length == v.dkLen do throwError "the {v.dkLen}-byte key has {v.dk.length} bytes"
    unless Spec.Pbkdf2.pbkdf2HmacSha256 v.p v.s v.c v.dkLen == some v.dk do
      throwError "PBKDF2-HMAC-SHA-256 of the RFC 7914 vector with c = {v.c} is wrong"

end VG.Test.Pbkdf2
