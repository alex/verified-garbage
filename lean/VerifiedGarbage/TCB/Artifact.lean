import VerifiedGarbage.TCB.Print

/-!
# Targets, contracts and verified artifacts

**Trusted.** This file defines what it *means* for an emitted function to be
verified. Every function the Rust crate contains is an `Artifact`, and an
`Artifact` cannot be constructed without a proof of `Verified`.

`Verified T c k` says, for the machine code `c` on target `T` and contract `k`:

1. **Total correctness and memory safety.** From every state satisfying
   `k.pre`, `c` terminates without faulting (so every memory access stays in
   the regions the state permits) in a state related to the initial one by
   `k.post` *and* by the target's calling-convention obligations
   `T.abiPreserved` (callee-saved registers, stack pointer, return address).
2. **Constant time.** Any two runs from `k.pre`-states that agree on public
   data (`k.pub`) have identical leakage traces (addresses and branches).
3. **Non-vacuity.** Some state satisfies `k.pre`. This is only a sanity
   check against an accidentally contradictory precondition; it does not
   replace reviewing the contract.

What a reviewer must read for each artifact is therefore: the ISA model and
ABI of its target (`TCB/<arch>/`), its contract (in `Spec/`), and its Rust
signature and documentation (in `Artifacts.lean`). The code and the proof
need not be read.
-/

namespace VG

/-- A code-generation target: an ISA model, its printer, and its calling convention. -/
structure Target where
  /-- Short name; also the name of the generated Rust module (e.g. `x86_64`). -/
  name : String
  isa : ISA
  printer : Printer isa
  /-- Calling-convention obligations every function must meet when it
  returns, relating the entry state to the exit state (callee-saved
  registers and the stack pointer restored, return address intact). -/
  abiPreserved : isa.State → isa.State → Prop
  /-- The Rust `cfg` predicate under which this target's functions are compiled. -/
  rustCfg : String
  /-- The Rust ABI string of the generated functions (e.g. `sysv64`). -/
  rustAbi : String

/-- The specification of one function. -/
structure Contract (M : ISA) where
  /-- Precondition on the entry state: argument registers, permitted memory
  regions, disjointness, CPU features, … -/
  pre : M.State → Prop
  /-- Postcondition relating the entry state to the exit state. -/
  post : M.State → M.State → Prop
  /-- When two entry states agree on everything public (e.g. lengths and
  pointers, but not keys or plaintexts). -/
  pub : M.State → M.State → Prop

/-- The proof obligation for emitting `c` on target `T` with contract `k`. -/
def Verified (T : Target) (c : Prog T.isa) (k : Contract T.isa) : Prop :=
  (∀ s, k.pre s → ∃ t s', Exec T.isa c s t s' ∧ T.abiPreserved s s' ∧ k.post s s') ∧
  ConstantTime T.isa k.pre k.pub c ∧
  (∃ s, k.pre s)

/-- A verified function, ready to be emitted into the Rust crate. -/
structure Artifact where
  target : Target
  /-- The Rust function name. Must be unique within the target; it is also
  the prefix of the function's local assembler labels. -/
  name : String
  /-- The Rust parameter list and return type, e.g. `(a: u64, b: u64) -> u64`.
  **Trusted**: it must agree with how `contract` reads the argument registers
  and writes the return register under `target`'s calling convention. -/
  rustSig : String
  /-- Documentation for the generated Rust function. It must state every
  requirement of `contract.pre` that the caller is responsible for. -/
  doc : String
  code : Prog target.isa
  contract : Contract target.isa
  verified : Verified target code contract

end VG
