import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-! Decode the reviewed ARM64 contract without requiring normalized upper bits. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.sp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .x0).setWidth 32).toNat ((s.gpr .x5).setWidth 32).toNat
  ((s.gpr .x6).setWidth 32).toNat ((s.gpr .x7).setWidth 32).toNat (abiWord s 72).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨abiWord s 8, (abiWord s 16).toNat⟩, ⟨abiWord s 24, (abiWord s 32).toNat⟩]
def abiMatrix (s : State) : Region := ⟨abiWord s 40, (abiWord s 48).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨abiWord s 56, 16384⟩
def abiOutput (s : State) : Region := ⟨abiWord s 64, (abiWord s 72).toNat⟩
def abiArguments (s : State) : Region := ⟨s.sp, 80⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (abiInputs s).map (·, false) ++ [(abiMatrix s, true), (abiWork s, true), (abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 400 ≤ (s.sp).toNat
  wrap : (s.sp).toNat + 80 ≤ 2 ^ 64
  rd : s.rd = abiInputs s ++ [abiArguments s]
  wr : s.wr = [abiMatrix s, abiWork s, abiOutput s]
  pairs : (abiBuffers s ++ [(abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [below (s.sp) 400],
    ∀ b ∈ abiBuffers s ++ [(abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .x0).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (abiParams s) (s.gpr .x2).toNat (s.gpr .x4).toNat
    (abiWord s 16).toNat (abiWord s 32).toNat
  threads : 1 ≤ ((abiWord s 0).setWidth 32).toNat ∧ ((abiWord s 0).setWidth 32).toNat < 2 ^ 24
  blocks : (abiWord s 48).toNat = (abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  all_goals simp only [BitVec.add_zero] at *
  constructor
  all_goals sig_eval [abiInputs, abiArguments, abiMatrix, abiWork, abiOutput, abiBuffers,
    abiWord, abiParams, below]
  all_goals try simp only [BitVec.add_zero]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.AArch64.Derive
