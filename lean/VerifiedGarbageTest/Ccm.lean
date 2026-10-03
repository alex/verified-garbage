import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Ccm

/-!
# Known-answer tests for the CCM specification

NIST CAVP AES-CCM vectors, read from the vendored response files under
`vectors/nist-cavp/ccm/` (see `vectors/sources/`) when this file is built
and checked against `VG.Spec.Ccm.aesCcmEncrypt` and
`VG.Spec.Ccm.aesCcmDecrypt`, so that a transcription error in the spec
fails the build. For each key length (128, 192 and 256 bits):

* the encryption files, which vary one length each (`VADT` the associated
  data's, 0 to 32 bytes; `VNT` the nonce's, 7 to 13 bytes; `VPT` the
  payload's, 0 to 24 bytes; `VTT` the MAC's, 4 to 16 bytes): the first
  vector of each section (one per length);
* the decryption files (`DVPT`), whose sections cover the extreme nonce and
  MAC lengths with empty and nonempty associated data and payloads: the
  first three vectors of each section, which the files mark `Pass` or
  `Fail`, and which include both.

(Evaluating the spec is slow; the Rust tests run the full Wycheproof suite
against the implementation.)
-/

namespace VG.Test.Ccm

open Lean Elab Command Test.Aes

/-- The records of a CAVP CCM response file: each `Count` starts a record,
which has the fields set before it in its section (by bracketed lines,
including several `k = v` separated by commas, by unbracketed `k = v` lines
before the first section, and by the `k = v` lines between a section's
header and its first record, such as `Key` and `Nonce`), followed by its own
fields. -/
def ccmRecords (text : String) : List (List (String × String)) := Id.run do
  let mut out : Array (List (String × String)) := #[]
  let mut globals : List (String × String) := []
  let mut sec : List (String × String) := []
  let mut cur : Option (List (String × String)) := none
  let mut started := false
  for l in text.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    if l.startsWith "[" then
      if let some r := cur then out := out.push r
      cur := none
      started := true
      let inner := (l.drop 1).takeWhile (· != ']') |>.toString
      sec := globals ++ (inner.splitOn ", ").filterMap fun kv => match kv.splitOn " = " with
        | [k, v] => some (k, v)
        | _ => none
      continue
    match l.splitOn " = " with
    | [k, v] =>
      if k == "Count" then
        if let some r := cur then out := out.push r
        cur := some sec
      match cur with
      | some r => cur := some (r ++ [(k, v)])
      | none => if started then sec := sec ++ [(k, v)] else globals := globals ++ [(k, v)]
    | _ => match cur with
      | some r => cur := some (r ++ [(l, "")])
      | none => pure ()
  if let some r := cur then out := out.push r
  return out.toList

/-- The last value of field `k` of a record. -/
def get (r : List (String × String)) (k : String) : Except String String :=
  match (r.filter (·.1 == k)).getLast? with
  | some (_, v) => pure v
  | none => throw s!"no `{k}`"

/-- A length field of a record. -/
def len (r : List (String × String)) (k : String) : Except String Nat := do
  match (← get r k).toNat? with
  | some n => pure n
  | none => throw s!"`{k}` is not a number"

/-- The bytes of field `k` of a record, which has `n` of them (the files
write `00` for an empty string). -/
def bytes (r : List (String × String)) (k : String) (n : Nat) : Except String (List Byte) := do
  if n == 0 then return []
  match Test.Sha256.unhex (← get r k) with
  | some bs => if bs.length == n then pure bs else throw s!"`{k}` is not {n} bytes"
  | none => throw s!"`{k}` is not hex"

/-- The first `k` records of each section, of a list of records: a section
is a run of records with the same lengths and key. -/
def firsts (k : Nat) (rs : List (List (String × String))) : List (List (String × String)) :=
  let key (r : List (String × String)) :=
    ["Alen", "Plen", "Nlen", "Tlen", "Key"].map fun k => (get r k).toOption
  let rec go : List (List (String × String)) → Option (List (Option String)) → Nat →
      List (List (String × String))
    | [], _, _ => []
    | r :: rs, prev, i =>
      let i := if prev == some (key r) then i else 0
      if i < k then r :: go rs (some (key r)) (i + 1) else go rs (some (key r)) (i + 1)
  go rs none 0

run_cmd do
  let mut n : Nat := 0
  for kind in ["VADT", "VNT", "VPT", "VTT"] do
    for bits in [128, 192, 256] do
      let name := s!"{kind}{bits}.rsp"
      for r in firsts 1 (ccmRecords (← readVectors "ccm" name)) do
        let v : Except String _ := do
          let (a, p) := (← len r "Alen", ← len r "Plen")
          let (nl, t) := (← len r "Nlen", ← len r "Tlen")
          pure (← bytes r "Key" (bits / 8), ← bytes r "Nonce" nl, ← bytes r "Adata" a,
            ← bytes r "Payload" p, ← bytes r "CT" (p + t), t)
        match v with
        | .error e => throwError "{name}, Count = {(get r "Count").toOption}: {e}"
        | .ok (key, nonce, aad, pt, ct, t) =>
          unless Spec.Ccm.aesCcmEncrypt key t nonce pt aad == some ct do
            throwError "{name}, Count = {(get r "Count").toOption}: encryption is wrong"
          n := n + 1
  -- One vector per length: 33 associated-data lengths, 7 nonce lengths, 25 payload lengths
  -- and 7 MAC lengths, for each of 3 key lengths.
  unless n == 3 * (33 + 7 + 25 + 7) do throwError "expected 216 vectors, checked {n}"

run_cmd do
  let mut pass : Nat := 0
  let mut fail : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"DVPT{bits}.rsp"
    for r in firsts 3 (ccmRecords (← readVectors "ccm" name)) do
      let v : Except String _ := do
        let (a, p) := (← len r "Alen", ← len r "Plen")
        let (nl, t) := (← len r "Nlen", ← len r "Tlen")
        let result ← get r "Result"
        let expected ← if result == "Pass" then some <$> bytes r "Payload" p
          else if result == "Fail" then pure none
          else throw s!"`Result = {result}`"
        pure (← bytes r "Key" (bits / 8), ← bytes r "Nonce" nl, ← bytes r "Adata" a,
          ← bytes r "CT" (p + t), t, expected)
      match v with
      | .error e => throwError "{name}, Count = {(get r "Count").toOption}: {e}"
      | .ok (key, nonce, aad, ct, t, expected) =>
        unless Spec.Ccm.aesCcmDecrypt key t nonce ct aad == expected do
          throwError "{name}, Count = {(get r "Count").toOption}: decryption-verification is wrong"
        if expected.isSome then pass := pass + 1 else fail := fail + 1
  -- 16 sections in each of 3 files.
  unless pass + fail == 144 && pass > 0 && fail > 0 do
    throwError "expected 144 decryption vectors of both outcomes, checked {pass} and {fail}"

end VG.Test.Ccm
