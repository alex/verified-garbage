import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-! Decode the reviewed System V contract without requiring normalized upper bits. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .rdi).setWidth 32).toNat ((s.gpr .r9).setWidth 32).toNat
  ((abiWord s 8).setWidth 32).toNat ((abiWord s 16).setWidth 32).toNat (abiWord s 96).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨abiWord s 32, (abiWord s 40).toNat⟩, ⟨abiWord s 48, (abiWord s 56).toNat⟩]
def abiMatrix (s : State) : Region := ⟨abiWord s 64, (abiWord s 72).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨abiWord s 80, 16384⟩
def abiOutput (s : State) : Region := ⟨abiWord s 88, (abiWord s 96).toNat⟩
def abiArguments (s : State) : Region := ⟨s.gpr .rsp + BitVec.ofNat 64 8, 96⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (abiInputs s).map (·, false) ++ [(abiMatrix s, true), (abiWork s, true), (abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 344 ≤ (s.gpr .rsp).toNat
  wrap : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  rd : s.rd = abiInputs s ++ [abiArguments s]
  wr : s.wr = [abiMatrix s, abiWork s, abiOutput s]
  pairs : (abiBuffers s ++ [(abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [⟨s.gpr .rsp, 8⟩, below (s.gpr .rsp) 344],
    ∀ b ∈ abiBuffers s ++ [(abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .rdi).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (abiParams s) (s.gpr .rdx).toNat (s.gpr .r8).toNat
    (abiWord s 40).toNat (abiWord s 56).toNat
  threads : 1 ≤ ((abiWord s 24).setWidth 32).toNat ∧ ((abiWord s 24).setWidth 32).toNat < 2 ^ 24
  blocks : (abiWord s 72).toNat = (abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [abiInputs, abiArguments, abiMatrix, abiWork, abiOutput, abiBuffers,
    abiWord, abiParams, below]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.X86_64.Derive
