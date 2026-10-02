import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Known-answer tests for HMAC, and SHA-256's functions

The HMAC-MD5 and HMAC-SHA-1 test cases of RFC 2202 (Sections 2 and 3) and
the HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384 and HMAC-SHA-512 ones of RFC 4231
(Section 4),
read from the vendored `vectors/rfc2202/rfc2202.txt` and
`vectors/rfc4231/rfc4231.txt` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Hmac.hmac` with the hash functions of
`Spec/Hmac.lean`, so that a transcription error (a wrong block size, say)
fails the build. (Section 3 of RFC 2202, as published, repeats parts of
its test cases 5 to 7 after test case 7; the first occurrence of each test
case is used.) The cases cover keys shorter than, equal to and longer than
a block, and messages of more than a block. A truncated MAC is compared with
the start of the computed one.

It also checks that the generic contracts of `Spec/Hmac/Generic.lean` and
`Spec/Pbkdf2/Generic.lean`, at SHA-256, are the HMAC-SHA-256 ones where they
have the same working space (`init` at 76 words, and the iteration, also at
`sha256I`), that `sha256I`'s functions have the names and modules of the
existing SHA-256 ones, and that each `Instance` names its own record and its
hash's `update` function, and has at least that function's working space
and its `finalize`'s. `init` for a key of any length (`initAnyKeyApi`) is
checked to be the same Rust function as `initApi`, with the same arguments
but for its working space.
-/

namespace VG.Test.Hmac

open Lean Elab Command
open Spec.Hmac (HashFunction hmac md5 sha1 sha224 sha256 sha384 sha512)

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- A test case: the key, the data and the (possibly truncated) MAC. -/
structure Case where
  key : List Byte
  data : List Byte
  mac : List Byte

/-- The lines of an RFC without its page footers and headers. -/
def body (text : String) (header : String) : List String :=
  (text.splitOn "\n").filter fun l => !(l.splitOn "[Page ").length > 1 && !l.startsWith header

/-! ## RFC 2202 -/

/-- A value of RFC 2202: `0x<hex>`, `0x<hh> repeated <n> times`, or a quoted string. -/
def value2202 (v : String) : Except String (List Byte) := do
  if v.startsWith "\"" then
    unless v.endsWith "\"" && v.length ≥ 2 do throw s!"unterminated string {v}"
    return ascii ((v.drop 1).dropEnd 1).toString
  match v.splitOn " repeated " with
  | [b, n] =>
    let some [x] := Test.Sha256.unhex (b.drop 2).toString | throw s!"bad byte {b}"
    let some k := (n.splitOn " ").head?.bind String.toNat? | throw s!"bad count {n}"
    return List.replicate k x
  | _ =>
    unless v.startsWith "0x" do throw s!"bad value {v}"
    let some bs := Test.Sha256.unhex (v.drop 2).toString | throw s!"bad hex {v}"
    return bs

/-- The fields of a section of RFC 2202, as `(name, value)`: a field starts
at the beginning of a line (`name =  value`, or `name  value`), and an
indented line continues the previous one's value. -/
def fields2202 (lines : List String) : List (String × String) :=
  lines.foldl (init := []) fun acc l =>
    if l.trimAscii.isEmpty then acc
    else if l.startsWith " " then
      match acc.reverse with
      | (n, v) :: rest => ((n, v ++ " " ++ l.trimAscii.toString) :: rest).reverse
      | [] => acc
    else
      let name := (l.splitOn " ").headD ""
      let rest := (l.drop name.length).trimAscii.toString
      let rest := if rest.startsWith "=" then (rest.drop 1).trimAscii.toString else rest
      acc ++ [(name, rest)]

/-- The test cases of the section of RFC 2202 between the lines `start` and `stop`. -/
def cases2202 (text start stop : String) : Except String (List Case) := do
  let lines := body text "RFC 2202"
  let some i := lines.findIdx? (· == start) | throw s!"no `{start}`"
  let sec := (lines.drop (i + 1)).takeWhile (· != stop)
  -- Group the fields by `test_case`, keeping the first group of each number.
  let groups := (fields2202 sec).foldl (init := ([] : List (String × List (String × String))))
    fun acc f =>
      if f.1 == "test_case" then acc ++ [(f.2, [])] else
        match acc.reverse with
        | (n, g) :: gs => gs.reverse ++ [(n, g ++ [f])]
        | [] => acc
  let firsts := groups.foldl (init := ([] : List (String × List (String × String)))) fun acc g =>
    if acc.any (·.1 == g.1) then acc else acc ++ [g]
  unless firsts.map (·.1) == (List.range 7).map (s!"{· + 1}") do
    throw s!"expected test cases 1 to 7, found {firsts.map (·.1)}"
  firsts.mapM fun (_, g) => do
    let get (n : String) : Except String String := match g.lookup n with
      | some v => pure v
      | none => throw s!"no `{n}` in {g}"
    let key ← value2202 (← get "key")
    let data ← value2202 (← get "data")
    let mac ← value2202 (← get "digest")
    let some kl := (← get "key_len").toNat? | throw "bad key_len"
    let some dl := (← get "data_len").toNat? | throw "bad data_len"
    unless key.length == kl && data.length == dl do throw s!"lengths disagree in {g}"
    return { key, data, mac }

/-! ## RFC 4231 -/

/-- The hex value of a field of RFC 4231 that starts on line `l` (after
` = `) or continues on it: its first word. -/
def hexWord (l : String) : Option String :=
  let w := (l.trimAscii.toString.splitOn " ").headD ""
  if !w.isEmpty && w.all Char.isHexDigit then some w else none

/-- The names of the fields of a test case of RFC 4231. -/
def names4231 : List String := ["Key", "Data", "HMAC-SHA-224", "HMAC-SHA-256", "HMAC-SHA-384", "HMAC-SHA-512"]

/-- The fields of a test case of RFC 4231, as `(name, hex)`: a line starting
with a field name, then `=` (missing after `Key` in test case 3 as
published) and a hex word, continued by the hex words that start the
following lines, up to a blank line or the next field. -/
def fields4231 (lines : List String) : List (String × String) :=
  (lines.foldl (init := (([] : List (String × String)), false)) fun (acc, open_) l =>
    let ws := (l.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    match ws with
    | n :: rest =>
      if names4231.contains n then
        let rest := if rest.head? == some "=" then rest.drop 1 else rest
        match rest.head?.bind hexWord with
        | some w => (acc ++ [(n, w)], true)
        | none => (acc, false)
      else match open_, hexWord l, acc.reverse with
        | true, some w, (n, v) :: rest => ((((n, v ++ w) :: rest).reverse), true)
        | _, _, _ => (acc, false)
    | [] => (acc, false)).1

/-- The test cases of RFC 4231 for the MAC named `name` (e.g. `HMAC-SHA-256`). -/
def cases4231 (text name : String) : Except String (List Case) := do
  let lines := body text "RFC 4231"
  let heads := (List.range 7).map fun i => s!"4.{i + 2}.  Test Case {i + 1}"
  heads.mapM fun h => do
    let some i := lines.findIdx? (·.trimAscii.toString == h) | throw s!"no `{h}`"
    let sec := (lines.drop (i + 1)).takeWhile fun l => !(l.startsWith "4." || l.startsWith "5.")
    let fs := fields4231 sec
    let get (n : String) : Except String (List Byte) := match fs.lookup n with
      | some v => match Test.Sha256.unhex v with
        | some bs => pure bs
        | none => throw s!"bad hex for `{n}` in {h}"
      | none => throw s!"no `{n}` in {h}"
    return { key := ← get "Key", data := ← get "Data", mac := ← get name }

/-! ## The checks -/

/-- Checks the cases against `hmac H`, with the MAC's full length `len`. -/
def check (what : String) (H : HashFunction) (len : Nat) (cs : List Case) : CommandElabM Unit := do
  unless cs.length == 7 do throwError "{what}: expected 7 test cases, found {cs.length}"
  for c in cs, i in List.range cs.length do
    let out := hmac H c.key c.data
    unless out.length == len do throwError "{what}: a MAC of {out.length} bytes, not {len}"
    unless c.mac.length == len || c.mac.length < len && i == 4 do
      throwError "{what}: test case {i + 1} has a {c.mac.length}-byte MAC"
    unless out.take c.mac.length == c.mac do throwError "{what}: test case {i + 1} is wrong"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Hmac.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let t2202 ← IO.FS.readFile (root / "vectors" / "rfc2202" / "rfc2202.txt")
  let t4231 ← IO.FS.readFile (root / "vectors" / "rfc4231" / "rfc4231.txt")
  let ok {α} (what : String) : Except String α → CommandElabM α
    | .ok a => pure a
    | .error e => throwError "{what}: {e}"
  check "HMAC-MD5" md5 16 (← ok "rfc2202.txt" (cases2202 t2202 "2. Test Cases for HMAC-MD5"
    "3. Test Cases for HMAC-SHA-1"))
  check "HMAC-SHA-1" sha1 20 (← ok "rfc2202.txt" (cases2202 t2202 "3. Test Cases for HMAC-SHA-1"
    "4. Security Considerations"))
  check "HMAC-SHA-224" sha224 28 (← ok "rfc4231.txt" (cases4231 t4231 "HMAC-SHA-224"))
  check "HMAC-SHA-256" sha256 32 (← ok "rfc4231.txt" (cases4231 t4231 "HMAC-SHA-256"))
  check "HMAC-SHA-384" sha384 48 (← ok "rfc4231.txt" (cases4231 t4231 "HMAC-SHA-384"))
  check "HMAC-SHA-512" sha512 64 (← ok "rfc4231.txt" (cases4231 t4231 "HMAC-SHA-512"))

/-! ## SHA-256's functions -/

open Spec.Hmac in
run_cmd do
  -- `sha256I`'s functions have the names and modules the Rust code uses.
  for (a, n, m) in [(sha256I.initApi, "vg_hmac_sha256_init", "hmac_sha256"),
      (sha256I.finalizeApi, "vg_hmac_sha256_finalize", "hmac_sha256"),
      (sha256I.iterateApi, "vg_pbkdf2_hmac_sha256_iterate", "pbkdf2_sha256")] do
    unless a.name == n && a.module == m do
      throwError "{a.module}::{a.name} is not {m}::{n}"
  unless sha256I.pbkdf2Api.name == "vg_pbkdf2_hmac_sha256" &&
      sha256I.pbkdf2Api.module == "pbkdf2_sha256" do
    throwError "{sha256I.pbkdf2Api.module}::{sha256I.pbkdf2Api.name}"

example : Spec.Pbkdf2.pbkdf2Hmac Spec.Hmac.sha256S = Spec.Pbkdf2.pbkdf2HmacSha256 := rfl

/-! ## The instances -/

open Spec.Hmac in
/-- Each instance, with its Lean name and the `Api` of its hash's `update`. -/
def instances : List (Spec.Hmac.Instance × String × Api) :=
  [(sha256I, "sha256I", Spec.Sha256.updateApi), (sha224I, "sha224I", Spec.Sha256.updateApi),
    (sha1I, "sha1I", Spec.Sha1.updateApi), (md5I, "md5I", Spec.Md5.updateApi),
    (sha384I, "sha384I", Spec.Sha512.updateApi), (sha512I, "sha512I", Spec.Sha512.updateApi),
    (sha512_224I, "sha512_224I", Spec.Sha512.updateApi),
    (sha512_256I, "sha512_256I", Spec.Sha512.updateApi)]

/-- The number of 64-bit words of the last parameter of `sig`, if it is an
array of them (the working space). -/
def scratchWords (sig : Sig) : Option Nat :=
  match sig.params.getLast? with
  | some (_, .array _ .u64 n) => some n
  | _ => none

run_cmd do
  for (I, lean, update) in instances do
    unless I.lean == lean do throwError "{lean} calls itself {I.lean}"
    unless I.update == update.name do throwError "{lean}: `update` is {update.name}, not {I.update}"
    let some w := scratchWords update.sig | throwError "{update.name} has no working space"
    unless w ≤ I.scratch do throwError "{lean}: {update.name} needs {w} words of working space"
  let names := instances.flatMap fun (I, _, _) =>
    [I.initApi.name, I.finalizeApi.name, I.iterateApi.name, I.pbkdf2Api.name]
  unless names.eraseDups.length == names.length do throwError "duplicate names: {names}"

/-! ## `init` for a key of any length -/

open Spec.Hmac in
/-- Each instance, with the `Api` of its hash's `finalize`. -/
def finalizes : List (Spec.Hmac.Instance × Api) :=
  [(sha256I, Spec.Sha256.finalizeApi), (sha224I, Spec.Sha256.finalizeApi),
    (sha1I, Spec.Sha1.finalizeApi),
    (md5I, Spec.Md5.finalizeApi), (sha384I, Spec.Sha512.finalizeApi),
    (sha512I, Spec.Sha512.finalizeApi), (sha512_224I, Spec.Sha512.finalizeApi),
    (sha512_256I, Spec.Sha512.finalizeApi)]

run_cmd do
  unless finalizes.map (·.1.lean) == instances.map (·.1.lean) do
    throwError "`finalizes` does not list the instances"
  for (I, finalize) in finalizes do
    -- `initAnyKeyApi` replaces `initApi`: the same Rust function, with the
    -- same arguments but for more working space, which also holds that of
    -- the hash's `finalize` (and, as `scratch` does, of its `update`), and
    -- a word for each byte of the streaming state.
    let a := I.initAnyKeyApi
    let b := I.initApi
    unless a.name == b.name && a.module == b.module do
      throwError "{a.module}::{a.name} is not {b.module}::{b.name}"
    unless a.sig.params.dropLast == b.sig.params.dropLast do
      throwError "{a.name}: the arguments differ from `initApi`'s"
    unless scratchWords a.sig == some (I.scratch + I.S.stateBytes) do
      throwError "{a.name}: working space is not {I.scratch + I.S.stateBytes} words"
    let some w := scratchWords finalize.sig | throwError "{finalize.name} has no working space"
    unless w ≤ I.scratch do throwError "{I.lean}: {finalize.name} needs {w} words of working space"
    unless finalize.name.replace "_finalize" "_update" == I.update do
      throwError "{I.lean}: {finalize.name} is not the `finalize` of {I.update}"

end VG.Test.Hmac
