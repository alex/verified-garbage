import VerifiedGarbage.TCB.Print
import VerifiedGarbage.TCB.Sig

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
signature (`Sig`) and documentation (in `Artifacts.lean`). The code and the proof
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
  /-- The calling convention that `rustAbi` stands for. -/
  abi : Abi isa

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

/-- The contract of a function with signature `sig` under the calling
convention `A`: the obligations the signature implies (see `TCB/Sig.lean`),
the further precondition `pre` and the postcondition `post`, both stated on
the arguments by name. If `writeArgs`, the function may also overwrite its
arguments passed in memory, where the calling convention gives them to the
callee; otherwise it may only read them. A calling convention that does not
model the arguments (`A.args` is `none`) gives an unsatisfiable
precondition, which `Verified` rejects. -/
def Sig.contract {M : ISA} (A : Abi M) (sig : Sig)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop) := Curry.const (fun _ => True) _)
    (post : sig.Post A.ptrBits) (writeArgs : Bool := false) : Contract M :=
  let ws := sig.words A.ptrBits
  let widths := ws.map (·.bits A.ptrBits)
  let pubs := sig.params.flatMap (·.2.pubs)
  { pre s := match A.args widths with
      | none => False
      | some vals =>
        let bufs := Sig.bufs sig.params (vals s)
        let all := bufs ++ (A.argArea widths s).map fun (r, w) => (r, w && writeArgs)
        A.wf widths s ∧
        A.rd s = (all.filter (!·.2)).map (·.1) ∧ A.wr s = (all.filter (·.2)).map (·.1) ∧
        all.Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
        (∀ r ∈ A.reserved s, ∀ a ∈ all, r.Disjoint a.1) ∧
        (∀ a ∈ bufs, a.1.base.toNat + a.1.len ≤ 2 ^ A.ptrBits) ∧
        Curry.apply ws pre (vals s) (A.mem s)
    post s s' := match A.args widths with
      | none => False
      | some vals => Curry.apply ws post (vals s) (A.mem s) (A.mem s')
          ((A.ret s').setWidth _)
    pub s₁ s₂ := match A.args widths with
      | none => False
      | some vals => A.pub s₁ s₂ ∧
        ∀ i, pubs.getD i false = true → (vals s₁).getD i 0 = (vals s₂).getD i 0 }

/-- The proof obligation for emitting `c` on target `T` with contract `k`. -/
def Verified (T : Target) (c : Prog T.isa) (k : Contract T.isa) : Prop :=
  (∀ s, k.pre s → ∃ t s', Exec T.isa c s t s' ∧ T.abiPreserved s s' ∧ k.post s s') ∧
  ConstantTime T.isa k.pre k.pub c ∧
  (∃ s, k.pre s)

/-- A verified function, ready to be emitted into the Rust crate. -/
structure Artifact where
  target : Target
  /-- The Rust module the function is emitted into, `src/asm/<target>/<module>.rs`
  (e.g. `sha256`). -/
  module : String
  /-- The Rust function name. Must be unique within the target. -/
  name : String
  /-- The Rust signature, rendered as the parameter list and return type
  (`Sig.rust`). **Trusted**: `contract` must read the arguments and write the
  return value where `target.abi` places them for `sig`, as the contracts
  `sig.contract target.abi …` do. -/
  sig : Sig
  /-- Documentation for the generated Rust function. It must state every
  requirement of `contract.pre` that the caller is responsible for. -/
  doc : String
  code : Prog target.isa
  contract : Contract target.isa
  verified : Verified target code contract

end VG
