import Lean.Data.Json
import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.MlKem

/-!
# Known-answer tests for the ML-KEM specification: the checks

NIST ACVP vectors for FIPS 203, read from the vendored `internalProjection.json`
files under `vectors/nist-acvp/` (see `vectors/sources/`) when the files
`MlKem512.lean`, `MlKem768.lean` and `MlKem1024.lean` are built, and checked
against `VG.Spec.MlKem`, so that a transcription error in the spec fails the
build. (Evaluating the spec is slow, so each parameter set is checked in a
file of its own, which Lake builds in parallel.) Each `SampleNTT` is bounded
by `minIterations`, which none of the vectors reaches.

For each of ML-KEM-512, ML-KEM-768 and ML-KEM-1024: the first vector of
`ML-KEM.KeyGen_internal`, the first valid ciphertext of
`ML-KEM.Decaps_internal` (which re-encrypts the decrypted message, and so
checks K-PKE.Encrypt too), and every vector of the encapsulation key check,
which include keys that fail it. For ML-KEM-768, the parameter set
implemented in assembly, also the first vector of `ML-KEM.Encaps_internal`
and the first modified ciphertext of `ML-KEM.Decaps_internal` (an implicit
rejection). The decapsulation key check has no spec (see
`Spec/MlKem.lean`), so its vectors are skipped. (Only these are checked
here; the Rust tests run the implementation on every vector.)
-/

namespace VG.Test.MlKem

open Lean Elab Command Spec.MlKem

/-- The vendored `vectors/nist-acvp/<dir>/internalProjection.json`. -/
def readVectors (dir : String) : CommandElabM Json := do
  -- This file is `lean/VerifiedGarbageTest/MlKem.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-acvp" / dir / "internalProjection.json")
  match Json.parse text with
  | .ok j => pure j
  | .error e => throwError "{dir}: {e}"

/-- The parameter set named `name`. -/
def params (name : String) : Option Params :=
  match name with
  | "ML-KEM-512" => some mlKem512
  | "ML-KEM-768" => some mlKem768
  | "ML-KEM-1024" => some mlKem1024
  | _ => none

/-- A test group: its parameter set, its `function` (empty for key
generation) and its test cases. -/
structure Group where
  params : Params
  name : String
  function : String
  tests : Array Json

/-- The test groups of an ACVP file. -/
def groups (j : Json) : Except String (List Group) := do
  let gs ← j.getObjValAs? (Array Json) "testGroups"
  gs.toList.mapM fun g => do
    let name ← g.getObjValAs? String "parameterSet"
    let some p := params name | throw s!"unknown parameter set {name}"
    let function := (g.getObjValAs? String "function").toOption.getD ""
    return { params := p, name, function, tests := ← g.getObjValAs? (Array Json) "tests" }

/-- The bytes written in hex in the field `key` of a test case. -/
def bytes (t : Json) (key : String) : Except String (List Byte) := do
  let s ← t.getObjValAs? String key
  let some bs := Test.Sha256.unhex s.toLower | throw s!"bad hex in {key}"
  return bs

/-- Runs `check` on each test group of the parameter set `name`, failing
with its error. -/
def checkGroups (name dir : String) (check : Group → Except String Unit) :
    CommandElabM Unit := do
  let gs ← match groups (← readVectors dir) with
    | .ok gs => pure gs
    | .error e => throwError "{dir}: {e}"
  let gs := gs.filter (·.name == name)
  if gs.isEmpty then throwError "{dir}: no {name} test group"
  for g in gs do
    match check g with
    | .ok () => pure ()
    | .error e => throwError "{dir}, {g.name} {g.function}: {e}"

/-- The test case of `g` whose field `key` is `value`, if any. -/
def find? (g : Group) (key value : String) : Option Json :=
  g.tests.find? fun t => (t.getObjValAs? String key).toOption == some value

/-- The sizes of Table 3, which the contracts of ML-KEM-768 write as
literals. -/
example : mlKem768.ekLen = 1184 ∧ mlKem768.dkLen = 2400 ∧ mlKem768.ctLen = 1088 := by decide

/-- Checks the spec against the vectors of the parameter set `name` (see
above); against all those listed above if `all`, and otherwise against those
of `ML-KEM.KeyGen_internal`, a valid ciphertext and the encapsulation key
check. -/
def check (name : String) (all : Bool) : CommandElabM Unit := do
  checkGroups name "ML-KEM-keyGen-FIPS203" fun g => do
    let some t := g.tests[0]? | throw "no test case"
    unless keyGenInternal g.params minIterations (← bytes t "d") (← bytes t "z") ==
        some (← bytes t "ek", ← bytes t "dk") do
      throw "KeyGen_internal is wrong"
  checkGroups name "ML-KEM-encapDecap-FIPS203" fun g => do
    match g.function with
    | "encapsulation" =>
      if !all then return
      let some t := g.tests[0]? | throw "no test case"
      unless encapsInternal g.params minIterations (← bytes t "ek") (← bytes t "m") ==
          some (← bytes t "k", ← bytes t "c") do
        throw "Encaps_internal is wrong"
    | "decapsulation" =>
      let reasons := ["valid decapsulation"] ++ if all then ["modified ciphertext"] else []
      for reason in reasons do
        let some t := find? g "reason" reason | throw s!"no {reason}"
        unless decapsInternal g.params minIterations (← bytes t "dk") (← bytes t "c") ==
            some (← bytes t "k") do
          throw s!"Decaps_internal is wrong on {reason}"
    | "encapsulationKeyCheck" =>
      for t in g.tests do
        unless ekCheck g.params (← bytes t "ek") == (← t.getObjValAs? Bool "testPassed") do
          throw s!"the encapsulation key check is wrong on {t.compress}"
    | "decapsulationKeyCheck" => pure ()
    | f => throw s!"unknown function {f}"

end VG.Test.MlKem
