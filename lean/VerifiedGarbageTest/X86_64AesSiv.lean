import VerifiedGarbage.Impl.AesSiv.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbageTest.Siv

/-! Model-level smoke checks of the x86-64 AES-SIV functions (with the AES-NI
implementation of AES), on both examples of RFC 5297 Appendix A: `init`,
`s2v_start`, `s2v_ad` of each component, `seal` (the output `V ‖ C`), then
`open` of it (returns 1 and the plaintext) and of it with `V` changed (returns 0
and zeros). Functional proofs accompany the artifacts; this catches
code-generation mistakes during development. -/

namespace VG.Test.X86_64AesSiv

open VG VG.X86_64
open Lean (Name)

/-- A bounded interpreter for model smoke tests, omitting leakage traces: the
semantics of `Exec`, with a call returning by `isa.ret` from the state after
the call. -/
def evaluate : Nat → Prog isa → State → Option State
  | 0, _, _ => none
  | _ + 1, .block is, s => runBlock isa is s
  | fuel + 1, .seq a b, s => (evaluate fuel a s).bind (evaluate fuel b)
  | fuel + 1, .ite c a b, s => do
    let taken ← isa.eval c s
    evaluate fuel (if taken then a else b) s
  | fuel + 1, .loop body c, s => do
    let s' ← evaluate fuel body s
    let again ← isa.eval c s'
    if again then evaluate fuel (.loop body c) s' else some s'
  | fuel + 1, .call _ body, s => do
    let s₁ ← isa.call s
    let s₂ ← evaluate fuel body s₁
    isa.ret s₁ s₂
  | fuel + 1, .frame push body pop, s => do
    let s₁ ← isa.push push s
    let s₂ ← evaluate fuel body s₁
    isa.pop pop s s₂

def key₀ : Addr := 0x1000
def ctx₀ : Addr := 0x2000
def d₀ : Addr := 0x2400
def scr₀ : Addr := 0x3000
def ad₀ : Addr := 0x4000
def data₀ : Addr := 0x5000
def work₀ : Addr := 0x7000

/-- The memory with `xs` written at `p`. -/
def put (m : Mem) (p : Addr) (xs : List Byte) : Mem := fun a =>
  if p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + xs.length then xs.getD (a.toNat - p.toNat) 0 else m a

def initial : State where
  gpr r := if r = .rsp then 0x9000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨key₀, 64⟩, ⟨ad₀, 4096⟩]
  wr := [⟨ctx₀, 512⟩, ⟨d₀, 16⟩, ⟨scr₀, 2560⟩, ⟨data₀, 4096⟩, ⟨work₀, 2560⟩, ⟨0x8000, 4096⟩]

def args (s : State) (xs : List (Reg × BitVec 64)) : State :=
  xs.foldl (fun s (r, v) => s.setReg r v) s

def c := Impl.Aes.X86_64.Ctr32.aesni
def e := Impl.Aes.X86_64.ExpandKey.aesni
def sfx := "_aesni"

def run (p : Prog isa) (s : State) (what : String := "") : Except String State :=
  match evaluate 1000000 p s with
  | some s' => pure s'
  | none => throw s!"{what} faulted"

/-- `D` after `s2v_start` and `s2v_ad` of each component. -/
def s2v (s : State) (rounds : Nat) (ads : List (List Byte)) : Except String State := do
  let mut s ← run (Impl.AesSiv.X86_64.s2vStart c sfx)
    (args s [(.rdi, ctx₀), (.rsi, BitVec.ofNat 64 rounds), (.rdx, d₀), (.rcx, scr₀)]) "s2v_start"
  for ad in ads do
    s := { s with mem := put s.mem ad₀ ad }
    s ← run (Impl.AesSiv.X86_64.s2vAd c sfx)
      (args s [(.rdi, ctx₀), (.rsi, BitVec.ofNat 64 rounds), (.rdx, d₀), (.rcx, ad₀),
        (.r8, BitVec.ofNat 64 ad.length), (.r9, scr₀)]) "s2v_ad"
  return s

def check (key : List Byte) (ads : List (List Byte)) (pt z : List Byte) : Except String Unit := do
  let rounds := key.length / 8 + 6
  let s := { initial with mem := put initial.mem key₀ key }
  let s ← run (Impl.AesSiv.X86_64.init e c sfx)
    (args s [(.rdi, key₀), (.rsi, BitVec.ofNat 64 key.length), (.rdx, ctx₀), (.rcx, scr₀)]) "init"
  unless Spec.Aes.bytesAt s.mem d₀ 0 = [] do throw "?"
  let s ← s2v s rounds ads
  unless Spec.Aes.bytesAt s.mem d₀ 16 ==
      Spec.Siv.s2vAcc (Spec.Siv.cmac (key.take (key.length / 2))) ads do
    throw "S2V of the associated data differs from the specification"
  let s := { s with mem := put s.mem data₀ pt }
  let s ← run (Impl.AesSiv.X86_64.«seal» c sfx)
    (args s [(.rdi, ctx₀), (.rsi, BitVec.ofNat 64 rounds), (.rdx, d₀), (.rcx, data₀),
      (.r8, BitVec.ofNat 64 pt.length), (.r9, work₀)]) "seal"
  unless Spec.Aes.bytesAt s.mem work₀ 16 ++ Spec.Aes.bytesAt s.mem data₀ pt.length == z do
    throw "seal differs from RFC 5297"
  for forge in [false, true] do
    let v := z.take 16
    let v := if forge then v.set 15 (v.getD 15 0 ^^^ 1) else v
    let s := { s with mem := put (put s.mem work₀ v) data₀ (z.drop 16) }
    let s ← s2v s rounds ads
    let s ← run (Impl.AesSiv.X86_64.«open» c sfx)
      (args s [(.rdi, ctx₀), (.rsi, BitVec.ofNat 64 rounds), (.rdx, d₀), (.rcx, data₀),
        (.r8, BitVec.ofNat 64 pt.length), (.r9, work₀)]) "open"
    let expected := if forge then List.replicate pt.length 0 else pt
    unless (s.gpr .rax).setWidth 32 == (if forge then 0 else 1) do throw s!"open returned {s.gpr .rax}"
    unless Spec.Aes.bytesAt s.mem data₀ pt.length == expected do throw "open left the wrong data"

run_cmd do
  let text := ((← Test.Siv.readFile ("rfc5297" / "rfc5297.txt")).splitOn "Appendix A.  Test Vectors")
  let text := text.getLastD ""
  let examples := [
    ("A.1.  Deterministic", "A.2.  Nonce-Based", ["AD"]),
    ("A.2.  Nonce-Based", "Author's Address", ["AD1", "AD2", "Nonce"])]
  for (start, stop, adLabels) in examples do
    let fs := Test.Siv.fields text start stop
    let get (label : String) : Lean.Elab.Command.CommandElabM (List Byte) := match fs.lookup label with
      | some v => pure v
      | none => throwError "RFC 5297 {start}: no `{label}`"
    match check (← get "Key") (← adLabels.mapM get) (← get "Plaintext") (← get "IV || C") with
    | .ok () => pure ()
    | .error err => throwError "x86-64 AES-SIV, RFC 5297 {start}: {err}"

-- Lengths at the edges of `finish`'s cases (`L < 16`, `L = 16`, `L > 16`, a
-- multiple of 16 or not) and of CTR's partial block, against the spec, with
-- 256- and 512-bit keys, and zero, one or two components of associated data.
run_cmd do
  for keyLen in [32, 64] do
    let key : List Byte := (List.range keyLen).map fun i => BitVec.ofNat 8 (7 * i + 3)
    for nAds in [0, 1, 2] do
      let ads : List (List Byte) := (List.range nAds).map fun j =>
        (List.range (5 + 13 * j)).map fun i => BitVec.ofNat 8 (i + j)
      for len in [0, 1, 15, 16, 17, 31, 32, 33, 48] do
        let pt : List Byte := (List.range len).map fun i => BitVec.ofNat 8 (3 * i + 1)
        match check key ads pt (Spec.Siv.encrypt key ads pt) with
        | .ok () => pure ()
        | .error err => throwError "x86-64 AES-SIV, {keyLen}-byte key, {nAds} components, {len} bytes: {err}"

end VG.Test.X86_64AesSiv
