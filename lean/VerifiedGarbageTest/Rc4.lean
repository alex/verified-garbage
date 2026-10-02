import Lean.Elab.Command
import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# RC4 specification tests

Reads every RFC 6229 §2 answer (14 keys, 18 offsets each) from the
unmodified published file in `vectors/rfc6229/`. Checks the full PRGA,
streaming continuation and decryption against those answers, including
indices wrapping at 256 and distant offsets through 4096. Generated
inputs exercise key-length boundaries and streaming identities; they are
not known-answer vectors.
-/

namespace VG.Test.Rc4

open Lean Elab Command Spec.Rc4

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

def start (key : List Byte) : Except String Spec.Rc4.Context :=
  (init key).mapError (fun e => s!"initialization: {repr e}")

def same (a b : Spec.Rc4.Context) : Bool :=
  a.table == b.table && a.i == b.i && a.j == b.j

def checkChunks (ctx : Spec.Rc4.Context) (input : List Byte) (splits : List Nat) :
    Except String Unit := do
  let (last, expected) := update ctx input
  for split in splits do
    let (first, a) := update ctx (input.take split)
    let (empty, nothing) := update first []
    unless same empty first && nothing.isEmpty do throw "empty update changed state"
    let (next, b) := update empty (input.drop split)
    unless a ++ b == expected && same next last do
      throw s!"streaming mismatch at split {split}"
  let mut next := ctx
  let mut output := []
  for byte in input do
    let (c, bs) := update next [byte]
    next := c
    output := output ++ bs
  unless output == expected && same next last do throw "byte-at-a-time mismatch"
  unless (finalize last).isEmpty do throw "finalization emitted bytes"

def checkRfc (text : String) : Except String Unit := do
  let mut keys := 0
  let mut answers := 0
  for record in (text.splitOn " Key length: ").drop 1 do
    let keyLines := (record.splitOn "\n").filterMap fun line =>
      match line.trimAscii.toString.splitOn "key: 0x" with
      | ["", value] => some value
      | _ => none
    unless keyLines.length == 1 do throw "expected one key per RFC record"
    let key ← unhex keyLines.head!
    let bits := ((record.splitOn " bits.").headD "").toNat?
    unless bits == some (8 * key.length) do throw "RFC key length mismatch"
    let ctx ← start key
    let zeros := List.replicate 4112 (0 : Byte)
    let (last, stream) := update ctx zeros
    unless last.i == BitVec.ofNat 8 zeros.length do throw "wrong final public index"
    let mut count := 0
    for line in record.splitOn "\n" do
      let line := line.trimAscii.toString
      unless line.startsWith "DEC" do continue
      let parts := line.splitOn ":"
      unless parts.length == 2 do throw "bad RFC answer line"
      let words := (parts.head!.splitOn " ").filter (!·.isEmpty)
      let some offset := (words[1]!).toNat? | throw "bad RFC decimal offset"
      let expected ← unhex parts[1]!
      unless expected.length == 16 && offset + 16 ≤ stream.length do
        throw "bad RFC answer length or offset"
      unless (stream.drop offset).take 16 == expected do
        throw s!"RFC keystream mismatch: {key.length}-byte key at {offset}"
      let (advanced, _) := update ctx (zeros.take offset)
      let (next, decrypted) := update advanced expected
      unless decrypted == List.replicate 16 0 do throw "RFC decryption mismatch"
      let (reference, _) := update ctx (zeros.take (offset + 16))
      unless same next reference do throw "RFC continuation state mismatch"
      count := count + 1
    unless count == 18 do throw s!"expected 18 answers for key, got {count}"
    checkChunks ctx (zeros.take 32) (List.range 33)
    checkChunks ctx zeros [0, 1, 255, 256, 257, 4096, 4112]
    keys := keys + 1
    answers := answers + count
  unless keys == 14 && answers == 252 do throw s!"incomplete RFC: {keys} keys/{answers} answers"

def checkLimits : Except String Unit := do
  for len in [0, 257] do
    match init (List.replicate len 0) with
    | .error .invalidKeyLength => pure ()
    | .ok _ => throw s!"accepted {len}-byte key"
  let input := (List.range 513).map fun i => BitVec.ofNat 8 (17 * i + 3)
  for len in [1, 2, 255, 256] do
    let key := (List.range len).map fun i => BitVec.ofNat 8 (i + 1)
    let ctx ← start key
    unless ctx.i == 0 && ctx.j == 0 do throw "PRGA indices not reset after KSA"
    unless ctx.table.toList.mergeSort (fun a b => a.toNat ≤ b.toNat) ==
        (List.range 256).map (BitVec.ofNat 8) do throw "KSA is not a permutation"
    let (last, encrypted) := update ctx input
    let (dec, decrypted) := update ctx encrypted
    unless decrypted == input && same last dec do throw "round trip failed"
    checkChunks ctx input [0, 1, 255, 256, 257, 512, 513]
  let ctx ← start [0]
  for index in [0, 1, 255] do
    unless swap ctx.table (BitVec.ofNat 8 index) (BitVec.ofNat 8 index) == ctx.table do
      throw "self-swap changed the table"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let rfc ← IO.FS.readFile (root / "vectors" / "rfc6229" / "rfc6229.txt")
  let result := do checkRfc rfc; checkLimits
  match result with
  | .ok () => pure ()
  | .error e => throwError "RC4: {e}"

#assert_standard_axioms VG.Spec.Rc4.initContract
#assert_standard_axioms VG.Spec.Rc4.applyContract

end VG.Test.Rc4
