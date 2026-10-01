import Lean.Elab.Command
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# Triple DES specification tests

Reads the unmodified NIST CAVP ECB response files under `vectors/`.
All 500 records are checked in both directions, including repeated keys
and two-key bundles. Multi-block records additionally exercise every
stream split, byte-at-a-time updates, empty updates and incomplete final
blocks. Synthetic inputs test key-length rejection and parity invariance;
they are not known-answer vectors.
-/

namespace VG.Test.TripleDes

open Lean Elab Command Spec.TripleDes

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

abbrev Fields := List (String × String)

def fields (text : String) : Fields :=
  (text.splitOn "\n").filterMap fun line =>
    match line.trimAscii.toString.splitOn " = " with
    | [k, v] => some (k, v)
    | _ => none

def get (fs : Fields) (k : String) : Except String String :=
  match fs.lookup k with
  | some v => pure v
  | none => throw s!"missing {k}"

def number (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {s}"

def block (bs : List Byte) : Except String Block := do
  unless bs.length == 8 do throw s!"not an 8-byte block: {bs.length}"
  return Vector.ofFn fun i => bs.getD i 0


def context (key : List Byte) (direction : Direction) : Except String Spec.TripleDes.Context :=
  (init key direction).mapError (fun e => s!"initialization: {repr e}")

def finalized (ctx : Spec.TripleDes.Context) : Bool :=
  match finalize ctx with | .ok bs => bs.isEmpty | .error _ => false

def incomplete (ctx : Spec.TripleDes.Context) : Bool :=
  match finalize ctx with | .error .incompleteBlock => true | _ => false

def checkStream (ctx : Spec.TripleDes.Context) (input expected : List Byte) : Except String Unit := do
  let empty := update ctx []
  unless empty.2.isEmpty && empty.1.schedule == ctx.schedule &&
      empty.1.direction == ctx.direction && empty.1.pending.isEmpty && finalized empty.1 do
    throw "empty initial update changed the context"
  for split in List.range (input.length + 1) do
    let (first, a) := update ctx (input.take split)
    unless a.length == 8 * (split / 8) && first.pending.length == split % 8 do
      throw s!"wrong buffering at split {split}"
    if split % 8 != 0 then
      unless incomplete first do throw "accepted a partial block"
    let (same, noOutput) := update first []
    unless noOutput.isEmpty && same.pending == first.pending &&
        same.schedule == first.schedule && same.direction == first.direction do
      throw "empty intermediate update changed the context"
    let (last, b) := update same (input.drop split)
    unless a ++ b == expected && finalized last do throw s!"wrong output at split {split}"
  let mut ctx := ctx
  let mut output := []
  for byte in input do
    let (next, out) := update ctx [byte]
    ctx := next
    output := output ++ out
  unless output == expected && finalized ctx do throw "byte-at-a-time streaming failed"

/-- KAT files use KEYs for three equal components; MMT files use KEY1–3. -/
def checkResponse (text : String) (stream : Bool) : Except String Nat := do
  let mut count := 0
  for record in text.replace "\r" "" |>.splitOn "\n\n" do
    let fs := fields record
    let some _ := fs.lookup "COUNT" | continue
    let key ← match fs.lookup "KEYs" with
      | some value => do
        let component ← unhex value
        unless component.length == 8 do throw "bad KEYs length"
        pure (component ++ component ++ component)
      | none => do
        let a ← unhex (← get fs "KEY1")
        let b ← unhex (← get fs "KEY2")
        let c ← unhex (← get fs "KEY3")
        unless a.length == 8 && b.length == 8 && c.length == 8 do throw "bad component length"
        pure (a ++ b ++ c)
    let pt ← unhex (← get fs "PLAINTEXT")
    let ct ← unhex (← get fs "CIPHERTEXT")
    unless pt.length % 8 == 0 && pt.length == ct.length do throw "bad ECB lengths"
    let enc ← context key .encrypt
    let dec ← context key .decrypt
    unless (update enc pt).2 == ct do throw s!"encryption failed at record {count}"
    unless (update dec ct).2 == pt do throw s!"decryption failed at record {count}"
    if stream then
      checkStream enc pt ct
      checkStream dec ct pt
    if key.take 8 == key.drop 16 then
      let short := key.take 16
      unless expandKey short == enc.schedule do throw "two-key and expanded three-key schedules differ"
      unless (update (← context short .encrypt) pt).2 == ct do throw "two-key encryption failed"
      unless (update (← context short .decrypt) ct).2 == pt do throw "two-key decryption failed"
    count := count + 1
  return count

def checkLimits : Except String Unit := do
  for len in List.range 33 do
    let key := (List.range len).map (fun i => BitVec.ofNat 8 (17 * i + 3))
    for direction in [Direction.encrypt, .decrypt] do
      match init key direction with
      | .error .invalidKeyLength =>
        if len == 16 || len == 24 then throw "rejected a valid key length"
      | .error _ => throw "wrong key-length error"
      | .ok ctx =>
        unless len == 16 || len == 24 do throw "accepted an invalid key length"
        unless expandKey (key.map (· ^^^ 1)) == ctx.schedule do throw "parity bits affected expansion"
        unless ctx.pending.isEmpty && finalized ctx do throw "initial context is not empty"
        for n in List.range 8 do
          let (next, out) := update ctx (List.replicate n 0)
          unless out.isEmpty && next.pending.length == n do throw "wrong partial-block buffering"
          unless (if n == 0 then finalized next else incomplete next) do
            throw "wrong partial-block finalization"
        unless ctx.schedule.toList.all (fun k => (k >>> 48) == 0) do
          throw "round key is not zero-extended"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let files := [
    ("nist-cavp-tdes-kat", "TECBsubtab.rsp", 38, false),
    ("nist-cavp-tdes-kat", "TECBpermop.rsp", 64, false),
    ("nist-cavp-tdes-kat", "TECBvarkey.rsp", 112, false),
    ("nist-cavp-tdes-kat", "TECBvartext.rsp", 128, false),
    ("nist-cavp-tdes-kat", "TECBinvperm.rsp", 128, false),
    ("nist-cavp-tdes-mmt", "TECBMMT2.rsp", 10, true),
    ("nist-cavp-tdes-mmt", "TECBMMT3.rsp", 20, true)]
  for (directory, name, expected, stream) in files do
    let text ← IO.FS.readFile (root / "vectors" / directory / name)
    match checkResponse text stream with
    | .error e => throwError "Triple DES {name}: {e}"
    | .ok count => unless count == expected do
        throwError "Triple DES {name}: expected {expected} records, got {count}"
  match checkLimits with
  | .ok () => pure ()
  | .error e => throwError "Triple DES: {e}"

#assert_standard_axioms VG.Spec.TripleDes.expandKeyContract
#assert_standard_axioms VG.Spec.TripleDes.encryptBlockContract
#assert_standard_axioms VG.Spec.TripleDes.decryptBlockContract
#assert_standard_axioms VG.Spec.TripleDes.ecbEncryptContract
#assert_standard_axioms VG.Spec.TripleDes.ecbDecryptContract

end VG.Test.TripleDes
