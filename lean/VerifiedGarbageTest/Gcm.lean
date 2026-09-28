import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Gcm

/-!
# Known-answer tests for the GCM specification

NIST CAVP AES-GCM vectors, read from the vendored response files under
`vectors/nist-cavp/gcm/` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Gcm.aesGcmEncrypt` and
`VG.Spec.Gcm.aesGcmDecrypt`, so that a transcription error in the spec
fails the build.

From each encryption file (128-, 192- and 256-bit keys), the first vector
of every section whose plaintext and additional data are both a partial
number of blocks (`PTlen = 408`, `AADlen = 720`) and whose tag is 128 or 32
bits: that covers every IV length (8, 96 and 1024 bits, so both ways of
forming `J₀`) and the longest and shortest tags. The decryption files mark
the vectors whose tag is wrong with `FAIL`; the first two vectors of each
such section with a 128-bit tag are checked, which include both outcomes.
(Evaluating the spec is slow; the Rust tests run the full Wycheproof suite
against the implementation.)
-/

namespace VG.Test.Gcm

open Lean Elab Command Test.Aes

/-- Whether a record is in a section with `PTlen = 408` and `AADlen = 720`
and a tag length in `tagLens`. -/
def selected (tagLens : List String) (r : Record) : Bool :=
  r.params.contains ("PTlen", "408") && r.params.contains ("AADlen", "720") &&
    tagLens.any fun t => r.params.contains ("Taglen", t)

/-- The first `k` records of each section (a run of records with the same
parameters) that `p` selects. -/
def firstOfSections (k : Nat) (p : Record → Bool) (rs : List Record) : List Record :=
  let rec go : List Record → Option (List (String × String)) → Nat → List Record
    | [], _, _ => []
    | r :: rs, prev, n =>
      let n := if prev == some r.params then n else 0
      if p r && n < k then r :: go rs (some r.params) (n + 1) else go rs (some r.params) n
  go rs none 0

run_cmd do
  let mut enc : Nat := 0
  let mut dec : Nat := 0
  let mut fails : Nat := 0
  for bits in [128, 192, 256] do
    let name := s!"gcmEncryptExtIV{bits}.rsp"
    for r in firstOfSections 1 (selected ["128", "32"]) (records (← readVectors "gcm" name)) do
      let v : Except String _ := do
        pure (← r.bytes "Key", ← r.bytes "IV", ← r.bytes "PT", ← r.bytes "AAD",
          ← r.bytes "CT", ← r.bytes "Tag")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok (key, iv, pt, aad, ct, tag) =>
        unless key.length == bits / 8 do throwError "{name}: a {key.length}-byte key"
        unless Spec.Gcm.aesGcmEncrypt key tag.length iv pt aad == (ct, tag) do
          throwError "{name}, {r.params}, Count = {(r.get "Count").toOption}: GCM-AE is wrong"
        enc := enc + 1
    let name := s!"gcmDecrypt{bits}.rsp"
    for r in firstOfSections 2 (selected ["128"]) (records (← readVectors "gcm" name)) do
      let v : Except String _ := do
        pure (← r.bytes "Key", ← r.bytes "IV", ← r.bytes "CT", ← r.bytes "AAD", ← r.bytes "Tag")
      match v with
      | .error e => throwError "{name}: {e}"
      | .ok (key, iv, ct, aad, tag) =>
        let expected ← if r.fail then pure none else
          match r.bytes "PT" with
          | .ok pt => pure (some pt)
          | .error e => throwError "{name}: {e}"
        unless Spec.Gcm.aesGcmDecrypt key tag.length iv ct aad tag == expected do
          throwError "{name}, {r.params}, Count = {(r.get "Count").toOption}: GCM-AD is wrong"
        dec := dec + 1
        if r.fail then fails := fails + 1
  -- 3 IV lengths × 2 tags (encrypting) or × 2 vectors (decrypting), for 3 key lengths.
  unless enc == 18 do throwError "expected 18 encryption vectors, checked {enc}"
  unless dec == 18 do throwError "expected 18 decryption vectors, checked {dec}"
  unless 0 < fails ∧ fails < dec do throwError "the decryption vectors checked are all {fails} FAIL"

end VG.Test.Gcm
