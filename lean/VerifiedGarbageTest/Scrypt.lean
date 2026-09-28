import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Scrypt

/-!
# Known-answer tests for the scrypt specification

The vectors of Sections 8–10 and 12 of RFC 7914, read from the vendored
`vectors/rfc7914/rfc7914.txt` (see `vectors/sources.toml`) when this file is
built and checked against `VG.Spec.Scrypt`, so that a transcription error in
the spec fails the build: the Salsa20/8 Core (§8), scryptBlockMix with
`r = 1` (§9), scryptROMix with `r = 1` and `N = 16` (§10), and the first
scrypt vector (§12), with `N = 16`, `r = 1` and `p = 1`. The other three
scrypt vectors (`N` up to 2²⁰, `r = 8`, `p` up to 16) are only parsed:
evaluating the spec cannot compute them in reasonable time. The Rust tests
run them against the implementation.
-/

namespace VG.Test.Scrypt

open Lean Elab Command

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The lines of section `n`, trimmed: from its heading to the next one.
Headings start in the first column (the table of contents is indented). -/
def section_ (lines : List String) (n : Nat) : Except String (List String) := do
  let some start := lines.findIdx? (·.startsWith s!"{n}.  ") | throw s!"no section {n}"
  return ((lines.drop (start + 1)).takeWhile (!·.startsWith s!"{n + 1}.  ")).map
    (·.trimAscii.toString)

/-- The bytes of the lines that are hex octets separated by spaces, after an
optional label ending with `=` (`B[0] =`): the octets in the text, in
order. Other lines (prose, labels, page breaks) are skipped. -/
def hexOf (lines : List String) : Except String (List Byte) := do
  let octets := lines.flatMap fun l =>
    let l := match l.splitOn "=" with | [_, v] => v | _ => l
    let ts := (l.splitOn " ").filter (!·.isEmpty)
    if !ts.isEmpty && ts.all (fun t => t.length == 2 && (Sha256.unhex t).isSome) then ts else []
  let some bs := Sha256.unhex (String.join octets) | throw "bad hex"
  return bs

/-- The lines of `sec` before and after the one starting with `out`. -/
def split (sec : List String) (out : String) : Except String (List String × List String) := do
  let some i := sec.findIdx? (·.startsWith out) | throw s!"no `{out}`"
  return (sec.take i, sec.drop (i + 1))

/-- A vector of §12: `scrypt (P="…", S="…", N=…, r=…, p=…, dklen=…) = …`. -/
structure Vector where
  pw : List Byte
  s : List Byte
  n : Nat
  r : Nat
  p : Nat
  dkLen : Nat
  dk : List Byte

/-- The text between `pre` and the next `post` in `t`. -/
def between (t pre post : String) : Except String String :=
  match t.splitOn pre with
  | [_, rest] => match rest.splitOn post with
    | v :: _ :: _ => pure v
    | _ => throw s!"no `{post}` after `{pre}` in {t}"
  | _ => throw s!"expected one `{pre}` in {t}"

def num (t pre post : String) : Except String Nat := do
  let some n := (← between t pre post).toNat? | throw s!"bad {pre} in {t}"
  return n

/-- The vectors of §12: the paragraphs that start with `scrypt (`. The RFC
spells the last parameter `dklen` in the first vector and `dkLen` in the
others. -/
def vectors (sec : List String) : Except String (List Vector) := do
  let paras := sec.splitBy fun a b => !a.isEmpty && !b.isEmpty
  let paras := paras.filter fun p => (p.headD "").startsWith "scrypt ("
  paras.mapM fun p => do
    let v := " ".intercalate p
    let [params, _] := v.splitOn ") =" | throw s!"no `) =` in {v}"
    let dkLen ← match params.splitOn "dklen=", params.splitOn "dkLen=" with
      | [_, d], _ | _, [_, d] => match d.trimAscii.toString.toNat? with
        | some d => pure d
        | none => throw s!"bad dkLen in {v}"
      | _, _ => throw s!"no dkLen in {v}"
    return { pw := ascii (← between v "P=\"" "\""), s := ascii (← between v "S=\"" "\""),
             n := ← num v "N=" ",", r := ← num v "r=" ",", p := ← num v "p=" ",", dkLen,
             dk := ← hexOf p.tail }

def check (b : Bool) (msg : String) : CommandElabM Unit := unless b do throwError msg

def run (text : String) : Except String (List (Bool × String)) := do
  let lines := text.splitOn "\n"
  -- §8: the Salsa20/8 Core.
  let (i, o) ← split (← section_ lines 8) "OUTPUT"
  let (i, o) := (← hexOf i, ← hexOf o)
  let salsa := [(i.length == 64 && o.length == 64, "§8 has 64-byte blocks"),
    (Spec.Scrypt.salsa i == o, "Salsa20/8 Core of the §8 vector is wrong")]
  -- §9: scryptBlockMix, r = 1.
  let (i, o) ← split (← section_ lines 9) "OUTPUT"
  let (i, o) := (← hexOf i, ← hexOf o)
  let blockMix := [(i.length == 128 && o.length == 128, "§9 has 128-byte blocks"),
    (Spec.Scrypt.blockMix 1 i == o, "scryptBlockMix of the §9 vector is wrong")]
  -- §10: scryptROMix, r = 1, N = 16.
  let (i, o) ← split (← section_ lines 10) "OUTPUT"
  let (i, o) := (← hexOf i, ← hexOf o)
  let roMix := [(i.length == 128 && o.length == 128, "§10 has 128-byte blocks"),
    (Spec.Scrypt.roMix 1 16 i == o, "scryptROMix of the §10 vector is wrong")]
  -- §12: scrypt.
  let vs ← vectors (← section_ lines 12)
  let shape := [(vs.map (fun v => (v.n, v.r, v.p)) ==
      [(16, 1, 1), (1024, 8, 16), (16384, 8, 1), (1048576, 8, 1)], "unexpected §12 vectors"),
    (vs.all fun v => v.dk.length == v.dkLen, "a §12 key has the wrong length")]
  let scrypt := (vs.filter (·.n == 16)).map fun v =>
    (Spec.Scrypt.scrypt v.pw v.s v.n v.r v.p v.dkLen == some v.dk, "scrypt of the first §12 vector is wrong")
  return salsa ++ blockMix ++ roMix ++ shape ++ scrypt

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Scrypt.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7914" / "rfc7914.txt")
  match run text with
  | .error e => throwError "rfc7914.txt: {e}"
  | .ok cs =>
    check (cs.length == 9) s!"expected 9 checks, got {cs.length}"
    for (ok, msg) in cs do check ok msg

end VG.Test.Scrypt
