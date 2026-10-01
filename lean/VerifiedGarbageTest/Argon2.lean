import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# Argon2 specification tests

Read the version 1.3 Argon2d, Argon2i and Argon2id vectors of RFC 9106 §5
from the byte-for-byte vendored RFC (`vectors/rfc9106/rfc9106.txt`). Check
H₀, all 24 published memory words for each variant (eight after each of
three passes), and the complete tag. No known-answer bytes are embedded
in this test. Boundary tests use these inputs and the algorithm's bounds.
-/

namespace VG.Test.Argon2

open Lean Elab Command Spec.Argon2

def check (b : Bool) (message : String) : Except String Unit :=
  unless b do throw message

def sectionLines (text : String) (n : Nat) : List String :=
  let lines := text.splitOn "\n"
  let start := s!"5.{n}.  "
  let stop := if n = 3 then "6.  " else s!"5.{n + 1}.  "
  (((lines.dropWhile (!·.startsWith start)).drop 1).takeWhile (!·.startsWith stop)).map
    (·.trimAscii.toString)

def afterLabel (lines : List String) (label : String) : Except String (String × List String) := do
  let first :: rest := lines.dropWhile (!·.startsWith label) | throw s!"missing {label}"
  let _ :: value :: _ := first.splitOn ":" | throw s!"missing colon in {first}"
  return (value.trimAscii.toString, rest)

def number (lines : List String) (label : String) : Except String Nat := do
  let fields := lines.flatMap fun line => (line.splitOn ",").map (·.trimAscii.toString)
  let (value, _) ← afterLabel fields label
  let some n := (value.splitOn " ").head!.toNat? | throw s!"bad number: {value}"
  return n

def hexLine (line : String) : Bool :=
  let tokens := (line.splitOn " ").filter (!·.isEmpty)
  !tokens.isEmpty && tokens.all (fun t => t.length == 2 && (Sha256.unhex t).isSome)

def bytes (lines : List String) (label : String) : Except String (List Byte) := do
  let (first, rest) ← afterLabel lines label
  let hex := String.join ((first :: rest.takeWhile hexLine).map fun l => l.replace " " "")
  let some bs := Sha256.unhex hex | throw s!"invalid hex after {label}"
  return bs

/-- Parse and check the byte count printed in an input label. -/
def input (lines : List String) (label : String) : Except String (List Byte) := do
  let some line := lines.find? (·.startsWith (label ++ "[")) | throw s!"missing {label}"
  let _ :: rest :: _ := line.splitOn "[" | throw s!"missing length in {line}"
  let some n := (rest.splitOn "]").head!.toNat? | throw s!"bad length in {line}"
  let bs ← bytes lines (label ++ "[")
  check (bs.length == n) s!"wrong length for {label}"
  return bs

/-- A published word: `Block 0031 [127]: c341b3ca45c10da5`. -/
def blockWord (line : String) : Except String (Nat × Nat × Word) := do
  let [position, value] := line.splitOn ":" | throw s!"bad block line {line}"
  let [block, word] := (position.drop 6).toString.splitOn "[" | throw s!"bad block index {line}"
  let some block := block.trimAscii.toString.toNat? | throw s!"bad block number {line}"
  let some word := ((word.splitOn "]").head!).trimAscii.toString.toNat?
    | throw s!"bad word number {line}"
  let some bs := Sha256.unhex value.trimAscii.toString | throw s!"bad word {line}"
  check (bs.length == 8) s!"word is not 64 bits: {line}"
  return (block, word, BitVec.ofNat 64 (bs.foldl (fun n b => 256 * n + b.toNat) 0))

def runVector (text : String) (sec : Nat) (variant : Variant) : Except String Unit := do
  let lines := sectionLines text sec
  let passes ← number lines "Passes:"
  let memory ← number lines "Memory:"
  let lanes ← number lines "Parallelism:"
  let tagLen ← number lines "Tag length:"
  let p : Params := { variant, passes, memory, lanes, tagLen }
  let password ← input lines "Password"
  let salt ← input lines "Salt"
  let secret ← input lines "Secret"
  let ad ← input lines "Associated data"
  check (decide (valid p password.length salt.length secret.length ad.length)) "invalid RFC parameters"
  let expectedH0 ← bytes lines "Pre-hashing digest:"
  let h0 := initialHash p password salt secret ad
  check (h0 == expectedH0 && h0.length == 64) s!"{repr variant}: H₀ mismatch"
  let mut state := initMemory p h0
  for pass in List.range p.passes do
    state := fillPass p state pass
    let snapshot := ((lines.dropWhile (· != s!"After pass {pass}:")).drop 1).takeWhile
      (fun l => !l.startsWith "After pass " && !l.startsWith "Tag:")
    let words ← (snapshot.filter (·.startsWith "Block ")).mapM blockWord
    check (words.length == 8) s!"{repr variant}: expected eight words after pass {pass}"
    for (block, word, expected) in words do
      let some b := state.memory[block]? | throw s!"block {block} out of bounds"
      let some actual := b.toArray[word]? | throw s!"word {word} out of bounds"
      check (actual == expected) s!"{repr variant}: pass {pass}, block {block}, word {word} mismatch"
  let expected ← bytes lines "Tag:"
  check (expected.length == p.tagLen) s!"{repr variant}: wrong published tag length"
  check (finish p state.memory == expected) s!"{repr variant}: tag mismatch"
  check (derive p password salt secret ad == expected) s!"{repr variant}: complete derivation mismatch"
  -- Every leaked address is a valid memory block. Argon2i leaks none.
  let refs := references p password salt secret ad
  check (refs.all fun index => index < p.blocks)
    s!"{repr variant}: out-of-bounds reference"
  if variant == .i then check refs.isEmpty "Argon2i leaked a secret-dependent address"
  else check (!refs.isEmpty) s!"{repr variant}: missing data-dependent references"
  -- H′ covers both sides of the 64-byte boundary and partial final chunks.
  for n in [1, 4, 32, 64, 65, 95, 96, 97, 1024] do
    check ((hPrime n password).length == n) s!"H′ output length {n} is wrong"
  -- Allocation rounds down, while the requested memory still affects H₀.
  let rounded := { p with memory := p.memory + 1 }
  check (rounded.blocks == p.blocks) "memory rounding changed the allocation"
  check (initialHash rounded password salt secret ad != h0) "H₀ ignored unrounded memory cost"
  check (!(decide (valid { p with lanes := 0 } 0 0 0 0))) "zero lanes accepted"
  check (!(decide (valid { p with passes := 0 } 0 0 0 0))) "zero passes accepted"
  check (!(decide (valid { p with memory := 8 * p.lanes - 1 } 0 0 0 0))) "too little memory accepted"
  check (!(decide (valid { p with tagLen := 3 } 0 0 0 0))) "short tag accepted"
  check (!(decide (valid p (2 ^ 32) 0 0 0))) "oversized password accepted"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc9106" / "rfc9106.txt")
  for (sec, variant) in [(1, Variant.d), (2, Variant.i), (3, Variant.id)] do
    match runVector text sec variant with
    | .ok () => pure ()
    | .error e => throwError "rfc9106.txt: {e}"

#assert_standard_axioms VG.Spec.Argon2.derive
#assert_standard_axioms VG.Spec.Argon2.deriveContract
#assert_standard_axioms VG.Spec.Argon2.hPrimeContract
#assert_standard_axioms VG.Spec.Argon2.compressContract

end VG.Test.Argon2
