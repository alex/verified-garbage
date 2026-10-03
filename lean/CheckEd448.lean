import Lean.Data.Json
import VerifiedGarbageTest.Ed448

/-!
Run the Ed448 specification against every Wycheproof vector:

    WYCHEPROOF_ROOT=/path/to/wycheproof lake env lean --run CheckEd448.lean

The build already checks the vendored RFC vectors. This additional check
uses the same external Wycheproof checkout as the Rust integration tests.
Wycheproof's Ed448 vectors have an empty context.
-/

open Lean VG VG.Spec.Ed448

private def bytes (obj : Json) (key : String) : Except String (List Byte) := do
  VG.Test.Ed448.hexBytes (← obj.getObjValAs? String key).toList

private def check (j : Json) : Except String Nat := do
  let mut count := 0
  for g in (← j.getObjValAs? (Array Json) "testGroups") do
    let pk ← bytes (← g.getObjVal? "publicKey") "pk"
    for t in (← g.getObjValAs? (Array Json) "tests") do
      let msg ← bytes t "msg"
      let sig ← bytes t "sig"
      let result ← t.getObjValAs? String "result"
      unless ["valid", "invalid", "acceptable"].contains result do
        throw s!"unknown result: {result}"
      let ok := verify pk [] msg sig
      if (result == "valid" && !ok) || (result == "invalid" && ok) then
        throw s!"tcId {← t.getObjValAs? Nat "tcId"}: expected {result}: \
          {← t.getObjValAs? String "comment"}"
      count := count + 1
  unless count > 0 && count == (← j.getObjValAs? Nat "numberOfTests") do
    throw s!"incorrect test count: {count}"
  return count

def main : IO Unit := do
  let some root ← IO.getEnv "WYCHEPROOF_ROOT"
    | throw (IO.userError "set WYCHEPROOF_ROOT to a C2SP/wycheproof checkout")
  let text ← IO.FS.readFile (System.FilePath.mk root / "testvectors_v1" / "ed448_test.json")
  match Json.parse text >>= check with
  | .ok n => IO.println s!"Ed448 specification passed {n} Wycheproof vectors"
  | .error e => throw (IO.userError e)
