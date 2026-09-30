import Lean.Elab.Command
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# RC2 specification tests

Reads all eight RFC 2268 §5 vectors, all seven OpenSSL 3.5.0 CBC vectors,
and pyca/cryptography's six-block CBC vector with a nonzero IV
from the unmodified published files under `vectors/` (provenance in
`vectors/sources/`). Both encryption and decryption are checked. Every
two-chunk split, byte-at-a-time updates, empty updates, final IVs and
incomplete final blocks are checked against those same published answers.

OpenSSL's generic RC2-CBC defaults to 128 effective bits, even for shorter
keys; RC2-40-CBC and RC2-64-CBC default to 40 and 64. `KeyBits` overrides
that default. These parameters are passed explicitly to the spec.
-/

namespace VG.Test.Rc2

open Lean Elab Command Spec.Rc2

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

def checkRfc (text : String) : Except String Unit := do
  -- Check every byte of PITABLE against its source as well as using the
  -- known answers to check the key expansion and all rounds together.
  let table := ((text.splitOn "   00: ").drop 1).headD ""
  let rows := (table.splitOn "\n").take 16
  let mut piBytes := []
  for row in rows do
    let value := (row.splitOn ": ").getLast!
    piBytes := piBytes ++ (← unhex value)
  unless piBytes == piTable.toList do throw "PITABLE differs from RFC 2268 §2"
  let excerpt := ((text.splitOn "5. Test vectors").drop 1).headD ""
  let excerpt := (excerpt.splitOn "6. RC2 Algorithm Object Identifier").headD ""
  let records := (excerpt.splitOn "   Key length (bytes) = ").drop 1
  unless records.length == 8 do throw s!"expected 8 RFC vectors, got {records.length}"
  for record in records do
    let fs := fields ("Key length (bytes) = " ++ record)
    -- The final vector's key wraps to a second line before the page break.
    let keyLines := (((record.splitOn "   Key = ").drop 1).headD "").splitOn "\n"
    let mut keyHex := keyLines.headD ""
    for line in keyLines.drop 1 do
      if !line.startsWith "         " then break
      keyHex := keyHex ++ line.trimAscii.toString
    let key ← unhex keyHex
    unless key.length == (← number (← get fs "Key length (bytes)")) do
      throw "RFC key length mismatch"
    let bits ← number (← get fs "Effective key length (bits)")
    let pt ← block (← unhex (← get fs "Plaintext"))
    let ct ← block (← unhex (← get fs "Ciphertext"))
    let k := expandKey key bits
    unless encryptBlock k pt == ct do throw s!"RFC encryption, {key.length} bytes/{bits} bits"
    unless decryptBlock k ct == pt do throw s!"RFC decryption, {key.length} bytes/{bits} bits"

def context (key iv : List Byte) (direction : Direction) (bits : Nat) : Except String Spec.Rc2.Context :=
  (initWithEffectiveBits key iv direction bits).mapError (fun e => s!"initialization: {repr e}")

def finalized (ctx : Spec.Rc2.Context) : Bool :=
  match finalize ctx with | .ok bs => bs.isEmpty | .error _ => false

def incomplete (ctx : Spec.Rc2.Context) : Bool :=
  match finalize ctx with | .error .incompleteBlock => true | _ => false

/-- Exercise streaming independently of how the published message is chunked. -/
def checkStream (ctx : Spec.Rc2.Context) (input expected nextIv : List Byte) : Except String Unit := do
  let empty := update ctx []
  unless empty.2.isEmpty && empty.1.iv == ctx.iv && empty.1.pending.isEmpty do
    throw "empty initial update changed the context"
  unless finalized empty.1 do throw "empty finalization failed"
  for split in List.range (input.length + 1) do
    let (first, a) := update ctx (input.take split)
    unless a.length == 8 * (split / 8) && first.pending.length == split % 8 do
      throw s!"wrong buffering at split {split}"
    if split % 8 != 0 then
      unless incomplete first do throw "accepted a partial block"
    let (same, noOutput) := update first []
    unless noOutput.isEmpty && same.iv == first.iv && same.pending == first.pending do
      throw "empty intermediate update changed the context"
    let (last, b) := update same (input.drop split)
    unless a ++ b == expected do throw s!"wrong streaming output at split {split}"
    unless last.iv.toList == nextIv do throw s!"wrong final IV at split {split}"
    unless finalized last do throw "complete blocks failed finalization"
  let mut ctx := ctx
  let mut output := []
  for byte in input do
    let (next, out) := update ctx [byte]
    ctx := next
    output := output ++ out
  unless output == expected && ctx.iv.toList == nextIv && finalized ctx do
    throw "byte-at-a-time streaming failed"

def checkOpenSsl (text : String) : Except String Unit := do
  let mut count := 0
  for record in text.splitOn "\n\n" do
    let fs := fields record
    let some cipher := fs.lookup "Cipher" | continue
    unless ["RC2-CBC", "RC2-40-CBC", "RC2-64-CBC"].contains cipher do continue
    let defaultBits := if cipher == "RC2-40-CBC" then 40
      else if cipher == "RC2-64-CBC" then 64 else 128
    let bits ← match fs.lookup "KeyBits" with
      | some value => number value
      | none => pure defaultBits
    let key ← unhex (← get fs "Key")
    let iv ← unhex (← get fs "IV")
    let pt ← unhex (← get fs "Plaintext")
    let ct ← unhex (← get fs "Ciphertext")
    unless pt.length % 8 == 0 && pt.length == ct.length do throw "bad CBC vector lengths"
    let nextIv := ct.drop (ct.length - 8)
    if let some value := fs.lookup "NextIV" then
      unless (← unhex value) == nextIv do throw "inconsistent published NextIV"
    checkStream (← context key iv .encrypt bits) pt ct nextIv
    checkStream (← context key iv .decrypt bits) ct pt nextIv
    count := count + 1
  unless count == 7 do throw s!"expected 7 OpenSSL CBC vectors, got {count}"

/-- The published pyca vector checks a nonzero IV and a longer chain than
the OpenSSL vectors. Its plaintext is already block-aligned, without padding. -/
def checkCryptography (text : String) : Except String Unit := do
  let fs := fields text
  unless fs.filter (·.1 == "COUNT") == [("COUNT", "0")] do
    throw "expected one pyca/cryptography vector"
  let key ← unhex (← get fs "Key")
  let iv ← unhex (← get fs "IV")
  let pt ← unhex (← get fs "Plaintext")
  let ct ← unhex (← get fs "Ciphertext")
  unless key.length == 16 && iv.any (· != 0) && pt.length == 48 && ct.length == 48 do
    throw "unexpected pyca/cryptography vector parameters"
  let nextIv := ct.drop (ct.length - 8)
  checkStream (← context key iv .encrypt 128) pt ct nextIv
  checkStream (← context key iv .decrypt 128) ct pt nextIv

/-- Generated inputs test limits and inverse/streaming properties; these
are not known-answer vectors. -/
def checkLimits : Except String Unit := do
  let iv := (List.range 8).map (BitVec.ofNat 8)
  let hasError (result : Except Error Spec.Rc2.Context) (expected : Error) : Bool :=
    match result with | .error e => e == expected | .ok _ => false
  for len in [0, 129] do
    unless hasError (init (List.replicate len 0) iv .encrypt) .invalidKeyLength do
      throw s!"accepted {len}-byte key"
  for bits in [0, 1025] do
    unless hasError (initWithEffectiveBits [0] iv .decrypt bits) .invalidEffectiveBits do
      throw s!"accepted {bits} effective bits"
  for len in [0, 7, 9] do
    unless hasError (init [0] (iv.take len ++ List.replicate (len - 8) 0) .encrypt)
        .invalidIvLength do throw s!"accepted {len}-byte IV"
  let data := (List.range 24).map (fun i => BitVec.ofNat 8 (17 * i + 3))
  for len in [1, 5, 8, 16, 128] do
    let key := (List.range len).map (fun i => BitVec.ofNat 8 (i + 1))
    let .ok defaultCtx := init key iv .encrypt | throw "valid default initialization failed"
    unless defaultCtx.schedule == expandKey key (8 * len) do throw "wrong default effective bits"
    for bits in [1, 7, 8, 9, 40, 63, 64, 128, 129, 1023, 1024] do
      let enc ← context key iv .encrypt bits
      let dec ← context key iv .decrypt bits
      let (_, ct) := update enc data
      let (last, pt) := update dec ct
      unless pt == data && finalized last do
        throw s!"round trip failed: {len}-byte key, {bits} effective bits"
      let empty := cbc enc.schedule .encrypt enc.iv []
      unless empty.1.isEmpty && empty.2 == enc.iv do throw "empty CBC changed IV"
      let empty := cbc dec.schedule .decrypt dec.iv []
      unless empty.1.isEmpty && empty.2 == dec.iv do throw "empty CBC decryption changed IV"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let rfc ← IO.FS.readFile (root / "vectors" / "rfc2268" / "rfc2268.txt")
  let evp ← IO.FS.readFile (root / "vectors" / "openssl-rc2" / "evpciph_rc2.txt")
  let pyca ← IO.FS.readFile (root / "vectors" / "cryptography-rc2" / "rc2-cbc.txt")
  let result := do checkRfc rfc; checkOpenSsl evp; checkCryptography pyca; checkLimits
  match result with
  | .ok () => pure ()
  | .error e => throwError "RC2: {e}"

#assert_standard_axioms VG.Spec.Rc2.expandKeyContract
#assert_standard_axioms VG.Spec.Rc2.encryptBlockContract
#assert_standard_axioms VG.Spec.Rc2.decryptBlockContract
#assert_standard_axioms VG.Spec.Rc2.cbcEncryptContract
#assert_standard_axioms VG.Spec.Rc2.cbcDecryptContract

end VG.Test.Rc2
