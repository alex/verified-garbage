import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Ocb

/-!
# Known-answer tests for the OCB specification

Read from RFC 7253, vendored unmodified under `vectors/rfc7253/` (see
`vectors/sources/`), when this file is built and checked against
`VG.Spec.Ocb`, so that a transcription error in the spec fails the build.
From Appendix A:

* the 16 `(N, A, P, C)` tuples with AES-128 and 128-bit tags (empty and
  nonempty associated data and plaintexts of 0 to 40 bytes), and the tuple
  with a 96-bit tag and another key: each checks `encrypt`, then that
  `decrypt` of `C` is `P`, and that it fails with the last byte of the tag
  changed;
* the internal values it gives for the last of the 16 (`L_*`, `L_$`, `L_0`,
  `L_1` and `Offset_0`);
* the iterated test, for AES-128 with 64-bit tags (a third tag length; its
  ~400 encryptions take half a minute to evaluate, so the other parameter
  sets are not run).
-/

namespace VG.Test.Ocb

open Lean Elab Command

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

/-- Whether `w` is a nonempty string of hex digits. -/
def isHex (w : String) : Bool := !w.isEmpty && w.all Char.isHexDigit

/-- The fields of Appendix A, in order: each `label : hex` or `label: hex`
line (the hex possibly empty), the hex continuing on the lines below that
hold nothing else. -/
def fields (text : String) : List (String × String) := Id.run do
  -- Appendix A itself, not its entry in the table of contents.
  let excerpt := (text.splitOn "Appendix A.  Sample Results").getLastD ""
  let excerpt := (excerpt.splitOn "Authors' Addresses").headD ""
  let mut out : Array (String × String) := #[]
  for l in excerpt.splitOn "\n" do
    if l.startsWith "Krovetz" || l.startsWith "RFC 7253 " then continue
    let t := l.trimAscii.toString
    match t.splitOn ":" with
    | [label, v] =>
      let label := label.trimAscii.toString
      let v := v.trimAscii.toString
      if !label.isEmpty && !label.contains ' ' || label.endsWith "Output" then
        out := out.push (label, v)
    | _ =>
      if isHex t && !out.isEmpty && l.startsWith "        " then
        out := out.modify (out.size - 1) fun (k, v) => (k, v ++ t)
  return out.toList

/-- The bytes of a hex field (in upper case, in the RFC). -/
def unhex (where_ v : String) : CommandElabM (List Byte) := match Test.Sha256.unhex v.toLower with
  | some bs => pure bs
  | none => throwError "RFC 7253 Appendix A, {where_}: `{v}` is not hex"

-- The tuples, and the internal values.
run_cmd do
  let fs := fields (← readFile ("rfc7253" / "rfc7253.txt"))
  let mut tupleKey : List Byte := []
  let mut tuple : List (String × String) := []
  let mut n : Nat := 0
  let mut tagLens : List Nat := []
  for (k, v) in fs do
    if k == "K" then tupleKey ← unhex "K" v
    if k == "N" || k == "A" || k == "P" then tuple := tuple ++ [(k, v)]
    if k == "C" then
      let get (l : String) : CommandElabM (List Byte) := match tuple.lookup l with
        | some v => unhex s!"tuple {n}" v
        | none => throwError "RFC 7253 Appendix A, tuple {n}: no `{l}`"
      let (nonce, a, p, c) := (← get "N", ← get "A", ← get "P", ← unhex s!"tuple {n}" v)
      let t := c.length - p.length
      unless Spec.Ocb.encrypt tupleKey t nonce a p == some c do
        throwError "RFC 7253 Appendix A, tuple {n}: encryption is wrong"
      unless Spec.Ocb.decrypt tupleKey t nonce a c == some p do
        throwError "RFC 7253 Appendix A, tuple {n}: decryption is wrong"
      let forged := c.set (c.length - 1) (c.getLast! ^^^ 1)
      unless Spec.Ocb.decrypt tupleKey t nonce a forged == none do
        throwError "RFC 7253 Appendix A, tuple {n}: decryption accepts a wrong tag"
      n := n + 1
      tagLens := tagLens ++ [t]
      tuple := []
  unless n == 17 && tagLens == List.replicate 16 16 ++ [12] do
    throwError "expected 16 tuples with 16-byte tags and one with a 12-byte tag, checked {tagLens}"
  -- The internal values, for the last of the 16 tuples (the first key, a 128-bit tag).
  let key ← unhex "K" ((fs.lookup "K").getD "")
  let get (l : String) : CommandElabM Spec.Ocb.Block := match fs.lookup l with
    | some v => Spec.Ocb.ofBytes <$> unhex l v
    | none => throwError "RFC 7253 Appendix A: no `{l}`"
  let lstar := Spec.Ocb.aes key 0
  unless lstar == (← get "L_*") do throwError "RFC 7253 Appendix A: L_* is wrong"
  unless Spec.Ocb.lDollar lstar == (← get "L_$") do throwError "RFC 7253 Appendix A: L_$ is wrong"
  unless Spec.Ocb.lAt lstar 0 == (← get "L_0") do throwError "RFC 7253 Appendix A: L_0 is wrong"
  unless Spec.Ocb.lAt lstar 1 == (← get "L_1") do throwError "RFC 7253 Appendix A: L_1 is wrong"
  let nonce ← unhex "N" ((fs.filter (·.1 == "N")).getD 15 ("", "")).2
  unless Spec.Ocb.offset0 (Spec.Ocb.aes key) 16 nonce == (← get "Offset_0") do
    throwError "RFC 7253 Appendix A: Offset_0 is wrong"

/-- The iterated test of Appendix A, for a key of `keyLen` bytes and a tag
of `t` bytes:
```
K = zeros(KEYLEN-8) || num2str(TAGLEN,8)
C = <empty string>
for i = 0 to 127 do
   S = zeros(8i)
   N = num2str(3i+1,96)
   C = C || OCB-ENCRYPT(K,N,S,S)
   N = num2str(3i+2,96)
   C = C || OCB-ENCRYPT(K,N,<empty string>,S)
   N = num2str(3i+3,96)
   C = C || OCB-ENCRYPT(K,N,S,<empty string>)
end for
N = num2str(385,96)
Output : OCB-ENCRYPT(K,N,C,<empty string>)
``` -/
def iterated (keyLen t : Nat) : Option (List Byte) := do
  let key := List.replicate (keyLen - 1) 0 ++ [BitVec.ofNat 8 (8 * t)]
  let num (x : Nat) : List Byte := (List.range 12).map fun i => BitVec.ofNat 8 (x / 256 ^ (11 - i))
  let mut c : List Byte := []
  for i in List.range 128 do
    let s := List.replicate i 0
    c := c ++ (← Spec.Ocb.encrypt key t (num (3 * i + 1)) s s)
    c := c ++ (← Spec.Ocb.encrypt key t (num (3 * i + 2)) [] s)
    c := c ++ (← Spec.Ocb.encrypt key t (num (3 * i + 3)) s [])
  Spec.Ocb.encrypt key t (num 385) c []

-- The iterated test.
run_cmd do
  let fs := fields (← readFile ("rfc7253" / "rfc7253.txt"))
  let mut n : Nat := 0
  for (bits, tagBits) in [(128, 64)] do
    let label := s!"AEAD_AES_{bits}_OCB_TAGLEN{tagBits} Output"
    let some v := fs.lookup label | throwError "RFC 7253 Appendix A: no `{label}`"
    let expected ← unhex label v
    unless iterated (bits / 8) (tagBits / 8) == some expected do
      throwError "RFC 7253 Appendix A: the iterated test for AES-{bits}, TAGLEN {tagBits} is wrong"
    n := n + 1
  unless n == 1 do throwError "expected 1 iterated test, checked {n}"

end VG.Test.Ocb
