import VerifiedGarbage.TCB.Artifact

/-!
# Rust signatures and the contract obligations they imply

**Trusted.** A `Sig` describes the Rust signature of a generated function in
terms the Rust type system gives meaning to: integers passed by value,
references to arrays (`&[T; N]`, `&mut [T; N]`) and slices (`&[T]`,
`&mut [T]`). `Sig.contract` turns it, with a target's calling convention
(`Abi`), into the parts of a `Contract` that every caller holding those
Rust values satisfies anyway, so that no contract has to spell them out:

* where each argument is (registers, stack slots, register pairs);
* the memory the function may read (every buffer, and arguments passed in
  memory) and write (every `mut` buffer);
* that a `mut` buffer overlaps no other buffer and no argument passed in
  memory, and that no buffer overlaps the return address (Rust's aliasing
  rules: a `&mut` is unique, and no Rust object contains the callee's
  return-address slot);
* that no buffer wraps around the end of the address space (no Rust
  allocation does);
* that the pointers, the slice lengths and the stack pointer are public.

A contract adds only what the types do not say: any further precondition
(e.g. a bound on a length), the postcondition, and which integer arguments
are public.
-/

namespace VG

/-- Element types of arrays and slices. -/
inductive Elem | u8 | u32 | u64
  deriving DecidableEq, Repr

def Elem.size : Elem → Nat | .u8 => 1 | .u32 => 4 | .u64 => 8
def Elem.rust : Elem → String | .u8 => "u8" | .u32 => "u32" | .u64 => "u64"

/-- Integer types passed by value. -/
inductive IntTy | u32 | u64 | usize
  deriving DecidableEq, Repr

/-- The width in bits, on a target with `ptrBits`-bit pointers. -/
def IntTy.bits (ptrBits : Nat) : IntTy → Nat | .u32 => 32 | .u64 => 64 | .usize => ptrBits
def IntTy.rust : IntTy → String | .u32 => "u32" | .u64 => "u64" | .usize => "usize"

/-- A parameter of a generated function. -/
inductive Param
  /-- An integer; `pub` says whether it is public for constant-time purposes. -/
  | int (ty : IntTy) (pub : Bool)
  /-- `&[T; n]`, or `&mut [T; n]` if `writable`. -/
  | array (writable : Bool) (elem : Elem) (n : Nat)
  /-- `&[T]`, or `&mut [T]` if `writable`, passed as a pointer and then a `usize`
  length (in elements) named `len`. -/
  | slice (writable : Bool) (elem : Elem) (len : String)
  deriving DecidableEq, Repr

structure Sig where
  params : List (String × Param)
  ret : Option IntTy := none
  deriving DecidableEq, Repr

/-- One machine-level argument: a pointer, or an integer of the given width. -/
inductive Word | addr | int (bits : Nat)
  deriving DecidableEq, Repr

def Word.bits (ptrBits : Nat) : Word → Nat | .addr => ptrBits | .int n => n

/-- What a contract sees of an argument: a pointer as an address, an integer
as a bit vector of its width. -/
abbrev Word.Ty : Word → Type | .addr => Addr | .int n => BitVec n

/-- The value of an argument from its zero-extended 64-bit form. -/
def Word.ofRaw : (w : Word) → BitVec 64 → w.Ty | .addr, v => v | .int n, v => v.setWidth n

/-- The machine-level arguments a parameter is passed as. -/
def Param.words (ptrBits : Nat) : Param → List Word
  | .int ty _ => [.int (ty.bits ptrBits)]
  | .array .. => [.addr]
  | .slice .. => [.addr, .int ptrBits]

def Sig.words (sig : Sig) (ptrBits : Nat) : List Word :=
  sig.params.flatMap fun p => p.2.words ptrBits

/-- `Curry ws α` is `w₁.Ty → … → wₙ.Ty → α`: contracts receive the arguments
by name, as the parameters of a function. -/
abbrev Curry : List Word → Type → Type
  | [], α => α
  | w :: ws, α => w.Ty → Curry ws α

def Curry.apply {α : Type} : (ws : List Word) → Curry ws α → List (BitVec 64) → α
  | [], f, _ => f
  | w :: ws, f, v :: vs => Curry.apply ws (f (w.ofRaw v)) vs
  | w :: ws, f, [] => Curry.apply ws (f (w.ofRaw 0)) []

def Curry.const {α : Type} (a : α) : (ws : List Word) → Curry ws α
  | [] => a
  | _ :: ws => fun _ => Curry.const a ws

/-- A calling convention: how the arguments of a function are passed, and
what the caller's frame looks like to it. -/
structure Abi (M : ISA) where
  /-- Pointer width. -/
  ptrBits : Nat
  /-- For arguments of the given widths (in bits), in order: their values on
  entry, zero-extended to 64 bits; `none` if the convention passes them in a
  way that is not modelled. -/
  args : List Nat → Option (M.State → List (BitVec 64))
  /-- The memory holding the arguments passed in memory (if any), and whether
  the callee may write it. -/
  argArea : List Nat → M.State → List (Region × Bool)
  /-- Memory that no buffer or argument area overlaps (the return address). -/
  reserved : M.State → List Region
  /-- Facts about the entry state that hold for every call (e.g. the part of
  the stack the function sees does not wrap around). -/
  wf : List Nat → M.State → Prop
  /-- The part of the state other than the arguments that is public (the
  stack pointer). -/
  pub : M.State → M.State → Prop
  /-- The memory of a state, and the regions it permits reading and writing. -/
  mem : M.State → Mem
  rd : M.State → List Region
  wr : M.State → List Region
  /-- The return value of the given width, zero-extended to 64 bits. -/
  ret : Nat → M.State → BitVec 64

/-- The buffers the parameters refer to, given the arguments' values, and
whether each is writable. -/
def Sig.bufs : List (String × Param) → List (BitVec 64) → List (Region × Bool)
  | [], _ => []
  | (_, .int ..) :: ps, _ :: vs => Sig.bufs ps vs
  | (_, .array m e n) :: ps, p :: vs => (⟨p, n * e.size⟩, m) :: Sig.bufs ps vs
  | (_, .slice m e _) :: ps, p :: l :: vs => (⟨p, l.toNat * e.size⟩, m) :: Sig.bufs ps vs
  | _, _ => []

/-- Whether each machine-level argument is public: pointers and lengths are. -/
def Param.pubs : Param → List Bool
  | .int _ pub => [pub]
  | .array .. => [true]
  | .slice .. => [true, true]

/-- The width of the return value (0 if there is none). -/
def Sig.retBits (sig : Sig) (ptrBits : Nat) : Nat := match sig.ret with
  | none => 0
  | some ty => ty.bits ptrBits

/-- The type of a postcondition: on the arguments, the memory on entry and
exit and the return value (of width 0 if there is none). -/
abbrev Sig.Post (sig : Sig) (ptrBits : Nat) : Type :=
  Curry (sig.words ptrBits) (Mem → Mem → BitVec (sig.retBits ptrBits) → Prop)

/-- The contract of a function with signature `sig` under the calling
convention `A`, whose further precondition is `pre` and postcondition `post`. -/
def Sig.contract {M : ISA} (A : Abi M) (sig : Sig)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop) := Curry.const (fun _ => True) _)
    (post : sig.Post A.ptrBits) : Contract M :=
  let ws := sig.words A.ptrBits
  let widths := ws.map (·.bits A.ptrBits)
  let pubs := sig.params.flatMap (·.2.pubs)
  { pre s := match A.args widths with
      | none => False
      | some vals =>
        let bufs := Sig.bufs sig.params (vals s)
        let all := bufs ++ A.argArea widths s
        A.wf widths s ∧
        A.rd s = (all.filter (!·.2)).map (·.1) ∧ A.wr s = (all.filter (·.2)).map (·.1) ∧
        all.Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
        (∀ r ∈ A.reserved s, ∀ a ∈ all, r.Disjoint a.1) ∧
        (∀ a ∈ bufs, a.1.base.toNat + a.1.len ≤ 2 ^ A.ptrBits) ∧
        Curry.apply ws pre (vals s) (A.mem s)
    post s s' := match A.args widths with
      | none => False
      | some vals => Curry.apply ws post (vals s) (A.mem s) (A.mem s')
          ((A.ret (sig.retBits A.ptrBits) s').setWidth _)
    pub s₁ s₂ := match A.args widths with
      | none => False
      | some vals => A.pub s₁ s₂ ∧
        ∀ i, pubs.getD i false = true → (vals s₁).getD i 0 = (vals s₂).getD i 0 }

/-! ## Rendering -/

def Param.rust (name : String) : Param → String
  | .int ty _ => s!"{name}: {ty.rust}"
  | .array w e n => s!"{name}: *{if w then "mut" else "const"} [{e.rust}; {n}]"
  | .slice w e len => s!"{name}: *{if w then "mut" else "const"} {e.rust}, {len}: usize"

/-- The Rust parameter list and return type. -/
def Sig.rust (sig : Sig) : String :=
  "(" ++ ", ".intercalate (sig.params.map fun p => p.2.rust p.1) ++ ")" ++
    match sig.ret with
    | none => ""
    | some ty => s!" -> {ty.rust}"

end VG
