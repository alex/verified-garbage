import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.Siv.Contract

/-!
# Known-answer tests for the AES-SIV specification

Read from RFC 5297, vendored unmodified under `vectors/rfc5297/` (see
`vectors/sources/`), when this file is built and checked against
`VG.Spec.Siv`, so that a transcription error in the spec fails the build:
both examples of Appendix A, deterministic (A.1: one component of
associated data, a plaintext shorter than a block, so `pad`) and
nonce-based (A.2: two components and a nonce, a plaintext of several
blocks, so `xorend`). Each checks S2V's first step (`CMAC(zero)`), its
result (`CMAC(final)`, `V`) and the output `IV || C` of `encrypt`; then that
`decrypt` of the output is the plaintext, and that it fails with the last
byte of `V` changed. The components, laid out in memory as a list of slices
with 64- and 32-bit descriptors, read back as themselves (`components`, the
associated data of `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`).
-/

namespace VG.Test.Siv

open Lean Elab Command

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

/-- Whether `w` is a group of at most 8 hex digits. -/
def isGroup (w : String) : Bool := !w.isEmpty && w.length ≤ 8 && w.all Char.isHexDigit

/-- The fields of an example of Appendix A, between `start` and `stop`: each
label (a line such as `Key:` or `CMAC(ad1)`, without its colon) and the hex
groups of the lines that follow it. -/
def fields (text start stop : String) : List (String × List Byte) := Id.run do
  let excerpt := (((text.splitOn start).drop 1).headD "").splitOn stop
  let mut out : Array (String × String) := #[]
  for l in (excerpt.headD "").splitOn "\n" do
    if l.startsWith "Harkins" || l.startsWith "RFC 5297 " then continue
    let words := (l.splitOn " ").filter (· ≠ "")
    if words.isEmpty || words.all (· == "-----") || words.all (· == "------------") then continue
    if words.all isGroup then
      if !out.isEmpty then
        out := out.modify (out.size - 1) fun (k, v) => (k, v ++ String.join words)
    else
      let label := l.trimAscii.toString
      out := out.push ((if label.endsWith ":" then label.dropEnd 1 else label).toString, "")
  return out.toList.filterMap fun (k, v) => (Test.Sha256.unhex v).map (k, ·)

/-- A memory holding the components `ads` from `0x10000` on, one every
`0x1000` bytes, and their descriptors at `0x100`: for each, its address and
its length, as `ptrBits`-bit little-endian words. -/
def layout (ptrBits : Nat) (ads : List (List Byte)) : Mem := fun a =>
  let w := ptrBits / 8
  let n := a.toNat
  if 0x100 ≤ n ∧ n < 0x100 + ads.length * (2 * w) then
    let k := n - 0x100
    let i := k / (2 * w)
    let j := k % (2 * w)
    let v := if j < w then 0x10000 + 0x1000 * i else (ads.getD i []).length
    BitVec.ofNat 8 (v / 256 ^ (j % w))
  else if 0x10000 ≤ n ∧ n < 0x10000 + 0x1000 * ads.length then
    let k := n - 0x10000
    (ads.getD (k / 0x1000) []).getD (k % 0x1000) 0
  else 0

run_cmd do
  -- Appendix A itself, not its entry in the table of contents.
  let text := ((← readFile ("rfc5297" / "rfc5297.txt")).splitOn "Appendix A.  Test Vectors")
  let text := text.getLastD ""
  let examples := [
    ("A.1.  Deterministic", "A.2.  Nonce-Based", ["AD"]),
    ("A.2.  Nonce-Based", "Author's Address", ["AD1", "AD2", "Nonce"])]
  for (start, stop, adLabels) in examples do
    let fs := fields text start stop
    let get (label : String) : CommandElabM (List Byte) := match fs.lookup label with
      | some v => pure v
      | none => throwError "RFC 5297 {start}: no `{label}`"
    let key ← get "Key"
    let ads ← adLabels.mapM get
    let pt ← get "Plaintext"
    let z ← get "IV || C"
    let mac := Spec.Siv.cmac (key.take (key.length / 2))
    unless key.length == 32 do throwError "RFC 5297 {start}: a {key.length}-byte key"
    unless Spec.Siv.s2vStart mac == (← get "CMAC(zero)") do
      throwError "RFC 5297 {start}: CMAC(zero) is wrong"
    unless Spec.Siv.s2v mac (ads ++ [pt]) == (← get "CMAC(final)") do
      throwError "RFC 5297 {start}: S2V is wrong"
    unless Spec.Siv.encrypt key ads pt == z do
      throwError "RFC 5297 {start}: encryption is wrong"
    unless Spec.Siv.decrypt key ads z == some pt do
      throwError "RFC 5297 {start}: decryption is wrong"
    let forged := z.set 15 (z.getD 15 0 ^^^ 1)
    unless Spec.Siv.decrypt key ads forged == none do
      throwError "RFC 5297 {start}: decryption accepts a wrong V"
    for ptrBits in [64, 32] do
      unless Spec.Siv.components ptrBits (layout ptrBits ads) 0x100 ads.length == ads do
        throwError "RFC 5297 {start}: the components do not read back with {ptrBits}-bit descriptors"

end VG.Test.Siv
