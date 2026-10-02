import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
import VerifiedGarbage.Proof.TripleDes.X86.Linear

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

noncomputable def inputLiterals : Array (Prog isa) :=
  #[input0.lit, input1.lit, input2.lit, input3.lit, input4.lit, input5.lit, input6.lit, input7.lit]
noncomputable def outputLiterals : Array (Prog isa) :=
  #[output0.lit, output1.lit, output2.lit, output3.lit, output4.lit, output5.lit, output6.lit, output7.lit]
def inputCfg : Cfg := { base := .ebp, slots := 128, ext := .edx, exts := 2 }
def inputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .edi then some (inWord 0) else none, slot := fun _ => none }
def inputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 32 + (47 - k)]
  else []
def inputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  linSlotPost 128 7 ((List.range 6).map fun j => (16 + j, inputBits i j)) e

theorem input_check : ∀ i < 8,
    check (lanes 32 7) inputCfg (linExt 1)
      (instrs (inputLiterals.getD i (.block []))) inputEnv (inputPost i) = true := by
  decide +kernel

def outputCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }
def outputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .esi then some (inWord 4) else none,
    slot := fun k => if 16 ≤ k ∧ k < 20 then some (inWord (k - 16)) else none }
def outputBits (i p : Nat) : List Nat :=
  [128 + p] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then [32 * j] else []
def outputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  linPost 8 [(.esi, outputBits i)] e
theorem output_check : ∀ i < 8,
    check (lanes 32 8) outputCfg (fun _ => none)
      (instrs (outputLiterals.getD i (.block []))) outputEnv (outputPost i) = true := by
  decide +kernel
end VG.Proof.TripleDes.X86
