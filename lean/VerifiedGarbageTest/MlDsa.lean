import Lean.Data.Json
import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# Known-answer tests for the ML-DSA specification: the checks

NIST ACVP vectors for FIPS 204, read from the vendored `internalProjection.json`
files under `vectors/nist-acvp/` (see `vectors/sources/`) when the files
`MlDsa44.lean`, `MlDsa65.lean` and `MlDsa87.lean` are built, and checked
against `VG.Spec.MlDsa`, so that a transcription error in the spec fails the
build. (Evaluating the spec is slow, so each parameter set is checked in a
file of its own, which Lake builds in parallel.) The loops are bounded by
`minBounds`, which none of the vectors reaches.

For each parameter set: the first vector of `ML-DSA.KeyGen_internal`; of
signature generation, the first vector of each test group of the internal
interface (`ML-DSA.Sign_internal`, with `μ` given or computed from the
message) and of the external interface of pure ML-DSA (`ML-DSA.Sign`, which
formats the message with its context string), deterministic and hedged; and
of signature verification, in each such test group, the first vector of
each reason a signature is valid or not. The contracts' leakage functions
are checked on the same vectors: signing's (`signLeak`) starts with `ρ` and
ends with the hint of the signature, each iteration's `c̃` tagged with
whether it was rejected. HashML-DSA has no spec, so its
test groups are skipped. (Only these are checked here; the Rust tests run
the implementation on every vector.)
-/

namespace VG.Test.MlDsa

open Lean Elab Command Spec.MlDsa

/-- The vendored `vectors/nist-acvp/<dir>/internalProjection.json`. -/
def readVectors (dir : String) : CommandElabM Json := do
  -- This file is `lean/VerifiedGarbageTest/MlDsa.lean`.
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
  | "ML-DSA-44" => some mlDsa44
  | "ML-DSA-65" => some mlDsa65
  | "ML-DSA-87" => some mlDsa87
  | _ => none

/-- A test group: its parameter set, its interface (`internal` or
`external`), its pre-hash mode (`none`, `pure` or `preHash`), whether `μ`
is given, whether signing is deterministic, and its test cases. -/
structure Group where
  params : Params
  name : String
  interface : String
  preHash : String
  externalMu : Bool
  deterministic : Bool
  tests : Array Json

/-- The test groups of an ACVP file. -/
def groups (j : Json) : Except String (List Group) := do
  let gs ← j.getObjValAs? (Array Json) "testGroups"
  gs.toList.mapM fun g => do
    let name ← g.getObjValAs? String "parameterSet"
    let some p := params name | throw s!"unknown parameter set {name}"
    return { params := p, name,
             interface := (g.getObjValAs? String "signatureInterface").toOption.getD ""
             preHash := (g.getObjValAs? String "preHash").toOption.getD ""
             externalMu := (g.getObjValAs? Bool "externalMu").toOption.getD false
             deterministic := (g.getObjValAs? Bool "deterministic").toOption.getD false
             tests := ← g.getObjValAs? (Array Json) "tests" }

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
    | .error e => throwError "{dir}, {g.name} {g.interface} {g.preHash}: {e}"

/-- The formatted message `M′` of a test case: its message, formatted with
its context string by the external interface, or as it is by the internal
one. -/
def formatted (g : Group) (t : Json) : Except String (List Byte) := do
  let M ← bytes t "message"
  if g.interface == "external" then
    let some M' := formatMessage (← bytes t "context") M | throw "context string too long"
    return M'
  return M

/-- The message representative `μ` of a test case: given (`externalMu`), or
computed from the public key hash `tr` and its formatted message. -/
def mu (g : Group) (t : Json) (tr : List Byte) : Except String (List Byte) := do
  if g.externalMu then bytes t "mu" else return messageRep tr (← formatted g t)

/-- Checks the spec against the vectors of the parameter set `name` (see
above). -/
def check (name : String) : CommandElabM Unit := do
  checkGroups name "ML-DSA-keyGen-FIPS204" fun g => do
    let some t := g.tests[0]? | throw "no test case"
    unless keyGenInternal g.params minBounds (← bytes t "seed") ==
        some (← bytes t "pk", ← bytes t "sk") do
      throw "KeyGen_internal is wrong"
    unless (keyGenLeak g.params (← bytes t "seed")).length ==
        32 + (g.params.ℓ + g.params.k) * 2 * maxBounds.rejBounded do
      throw "keyGenLeak is wrong"
  checkGroups name "ML-DSA-sigGen-FIPS204" fun g => do
    if g.preHash == "preHash" then return
    let some t := g.tests[0]? | throw "no test case"
    let sk ← bytes t "sk"
    let rnd ← if g.deterministic then pure (List.replicate 32 0) else bytes t "rnd"
    let μ ← mu g t (skTr sk)
    let σ ← bytes t "signature"
    unless signMu g.params minBounds sk μ rnd == some σ do
      throw "Sign_internal is wrong"
    -- What the contract lets signing leak ends with the hint of the signature.
    let some h := (sigDecode g.params σ).2.2 | throw "the signature's hint is malformed"
    let leak := signLeak g.params sk μ rnd
    -- `ρ`, then each iteration's `c̃` and 0 (rejected), then the last one's
    -- `c̃`, 1 and hint.
    let hint := h.flatMap (·.toList.map Bool.toNat)
    let iters := (leak.length - 32 - hint.length) / (g.params.ctildeLen + 1)
    unless leak.take 32 == leakBytes (sk.take 32) && leak.drop (leak.length - hint.length) == hint &&
        32 + iters * (g.params.ctildeLen + 1) + hint.length == leak.length &&
        (List.range iters).all (fun i =>
          leak.getD (32 + (i + 1) * (g.params.ctildeLen + 1) - 1) 2 == if i + 1 = iters then 1 else 0) do
      throw "signLeak is wrong"
  checkGroups name "ML-DSA-sigVer-FIPS204" fun g => do
    if g.preHash == "preHash" then return
    let mut seen : List String := []
    for t in g.tests do
      let reason ← t.getObjValAs? String "reason"
      if reason ∈ seen then continue
      seen := reason :: seen
      let pk ← bytes t "pk"
      unless verifyMu g.params minBounds pk (← mu g t (pkTr pk)) (← bytes t "signature") ==
          some (← t.getObjValAs? Bool "testPassed") do
        throw s!"Verify_internal is wrong on {reason}"
    if seen.length < 4 then throw s!"only the reasons {seen}"

end VG.Test.MlDsa
