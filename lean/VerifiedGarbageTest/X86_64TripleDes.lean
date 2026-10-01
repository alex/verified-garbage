import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Impl.TripleDes.X86_64.Ecb
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbageTest.TripleDes

/-! Model-level smoke checks of the complete scalar functions, using the
published NIST files. Functional proofs and Rust vector tests accompany the
final artifacts; this catches code-generation mistakes during development. -/

namespace VG.Test.X86_64TripleDes

open VG VG.X86_64

/-- A bounded interpreter for model smoke tests, omitting leakage traces. -/
def evaluate : Nat → Prog isa → State → Option State
  | 0, _, _ => none
  | fuel + 1, .block is, s => runBlock isa is s
  | fuel + 1, .seq a b, s => (evaluate fuel a s).bind (evaluate fuel b)
  | fuel + 1, .ite c a b, s => do
    let taken ← isa.evalCond c s
    evaluate fuel (if taken then a else b) s
  | fuel + 1, .loop body c, s => do
    let s' ← evaluate fuel body s
    let again ← isa.evalCond c s'
    if again then evaluate fuel (.loop body c) s' else some s'
  | fuel + 1, .call _ body, s => do
    let s₁ ← isa.call s
    let s₂ ← evaluate fuel body s₁
    isa.ret s s₂
  | fuel + 1, .frame push body pop, s => do
    let s₁ ← isa.push push s
    let s₂ ← evaluate fuel body s₁
    isa.pop pop s s₂

def initial (key input : List Byte) : State where
  gpr r := if r = .rdi then 0x1000 else if r = .rsi then BitVec.ofNat 64 key.length
    else if r = .rdx then 0x2000 else if r = .rcx then 0x3000 else if r = .rsp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x1000 + key.length then
    key.getD (a.toNat - 0x1000) 0
    else if 0x4000 ≤ a.toNat ∧ a.toNat < 0x4000 + input.length then
    input.getD (a.toNat - 0x4000) 0 else 0
  rd := [⟨0x1000, key.length⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 1024⟩, ⟨0x4000, input.length⟩, ⟨0x5000, 4096⟩]

def checkCase (key pt ct : List Byte) : Except String Unit := do
  let some s := evaluate 128 Impl.TripleDes.X86_64.Key.expandKey (initial key pt)
    | throw "key expansion faulted"
  unless Spec.TripleDes.scheduleAt s.mem 0x2000 == Spec.TripleDes.expandKey key do
    throw "key expansion differs from the specification"
  let enc := (s.setReg .rdi 0x2000).setReg .rsi 0x4000 |>.setReg .rdx 0x3000
  let some encrypted := evaluate 128 Impl.TripleDes.X86_64.encryptBlock enc
    | throw "block encryption faulted"
  unless Spec.TripleDes.bytesAt encrypted.mem 0x4000 pt.length == ct do
    throw "block encryption differs from NIST"
  let some decrypted := evaluate 128 Impl.TripleDes.X86_64.decryptBlock encrypted
    | throw "block decryption faulted"
  unless Spec.TripleDes.bytesAt decrypted.mem 0x4000 pt.length == pt do
    throw "block decryption differs from NIST"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-tdes-mmt" / "TECBMMT3.rsp")
  let record := ((text.replace "\r" "" |>.splitOn "COUNT = ").drop 1).headD ""
  let fs := TripleDes.fields ((record.splitOn "\n\n").headD "")
  let result := do
    let a ← TripleDes.unhex (← TripleDes.get fs "KEY1")
    let b ← TripleDes.unhex (← TripleDes.get fs "KEY2")
    let c ← TripleDes.unhex (← TripleDes.get fs "KEY3")
    let pt ← TripleDes.unhex (← TripleDes.get fs "PLAINTEXT")
    let ct ← TripleDes.unhex (← TripleDes.get fs "CIPHERTEXT")
    checkCase (a ++ b ++ c) pt ct
  match result with
  | .ok () => pure ()
  | .error e => throwError "x86-64 Triple DES: {e}"

end VG.Test.X86_64TripleDes
