import VerifiedGarbageTest.Cmac
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.TCB.Axioms

/-!
# Known-answer tests for TDEA-CMAC (3DES-CMAC)

Read from the unmodified NIST CAVP CMAC response files under
`vectors/nist-cavp/cmac-tdes/` (provenance in `vectors/sources/`) when this
file is built, and checked against `VG.Spec.Cmac.tdesCmac`, so that a
transcription error in the spec fails the build:

* Generation, for two- and three-key TDEA: the first vector of every message
  and MAC length. These cover empty messages, complete and partial last
  blocks, and MACs of 5 to 8 bytes.
* Verification, for two- and three-key TDEA: the first two vectors of every
  message and MAC length but the 65536-byte messages, checking
  `VG.Spec.Cmac.verify`; they include both outcomes.

Every record's key is `Key1 ‖ Key2 ‖ Key3` (the files give all three, also
for two-key TDEA, where some failing records change `Key3`); where
`Key3 = Key1`, the 16-byte key `Key1 ‖ Key2` is checked to give the same
result.
-/

namespace VG.Test.CmacTripleDes

open Lean Elab Command Test.Aes Test.Cmac

/-- The 24-byte key `Key1 ‖ Key2 ‖ Key3` of a record, and the 16-byte key
`Key1 ‖ Key2` if `Key3 = Key1`. -/
def keys (r : Record) : Except String (List Byte × Option (List Byte)) := do
  let k1 ← r.bytes "Key1"
  let k2 ← r.bytes "Key2"
  let k3 ← r.bytes "Key3"
  unless k1.length == 8 && k2.length == 8 && k3.length == 8 do throw "a key that is not 8 bytes"
  return (k1 ++ k2 ++ k3, if k3 == k1 then some (k1 ++ k2) else none)

run_cmd do
  let mut n : Nat := 0
  for k in [2, 3] do
    let name := s!"CMACGenTDES{k}.rsp"
    for r in firstOfLengths 1 (fun _ => true) (records (← readVectors "cmac-tdes" name)) do
      let v : Except String _ := do pure (← keys r, ← message r, ← r.bytes "Mac")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok ((key, short), msg, t) =>
        unless Spec.Cmac.tdesCmac key t.length msg == t do
          throwError "{name}, Count = {(r.get "Count").toOption}: CMAC generation is wrong"
        if let some key := short then
          unless Spec.Cmac.tdesCmac key t.length msg == t do
            throwError "{name}, Count = {(r.get "Count").toOption}: two-key CMAC generation is wrong"
        else if k == 2 then throwError "{name}: a two-key record with Key3 ≠ Key1"
        n := n + 1
  unless n == 20 do throwError "expected 20 generation vectors, checked {n}"

run_cmd do
  let mut pass : Nat := 0
  let mut fail : Nat := 0
  for k in [2, 3] do
    let name := s!"CMACVerTDES{k}.rsp"
    let rs := records (← readVectors "cmac-tdes" name)
    for r in firstOfLengths 2 (fun r => (r.get "Mlen").toOption != some "65536") rs do
      let v : Except String _ := do
        pure (← keys r, ← message r, ← r.bytes "Mac", ← r.get "Result")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok ((key, short), msg, t, result) =>
        let valid := result == "P"
        unless valid || result.startsWith "F" do throwError "{name}: `Result = {result}`"
        unless Spec.Cmac.verify (Spec.Cmac.tdes key) 8 msg t == valid do
          throwError "{name}, Count = {(r.get "Count").toOption}: CMAC verification is wrong"
        if let some key := short then
          unless Spec.Cmac.verify (Spec.Cmac.tdes key) 8 msg t == valid do
            throwError "{name}, Count = {(r.get "Count").toOption}: two-key CMAC verification is wrong"
        if valid then pass := pass + 1 else fail := fail + 1
  unless pass == 14 && fail == 42 do
    throwError "expected 14 valid and 42 invalid verification vectors, checked {pass} and {fail}"

#assert_standard_axioms VG.Spec.Cmac.tdesInitContract
#assert_standard_axioms VG.Spec.Cmac.tdesUpdateContract
#assert_standard_axioms VG.Spec.Cmac.tdesFinalizeContract

end VG.Test.CmacTripleDes
