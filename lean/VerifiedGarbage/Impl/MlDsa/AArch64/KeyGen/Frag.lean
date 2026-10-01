import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on AArch64: the pieces of the top-level functions

`vg_mldsa*_keygen` and `vg_mldsa*_verify` are sequences of calls of ML-DSA's
polynomial primitives (`vg_mldsa_*`, `Spec/MlDsa/Poly.lean`) and of the SHA-3
sponge functions, on buffers in their working space `scratch` (whose address
they keep in `x28`) and their arguments (whose addresses they keep in `x25`,
`x26` and `x27`): callee-saved registers, which the functions they call keep.
They keep the AND of the results of the calls so far in `x24`, and save
their caller's `x24`–`x28` and `x30` (the return address, which each call
overwrites) in `scratch`, at `SV`; they use no stack of their own.

A buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into their registers
(`glue`: an `add`, or a `movz`, `movk` and `add`, for a pointer; a `movz`
and `movk` for an integer).

The code is generic in the primitives it calls (`Prims`, their code), so
that it can be proven for any implementations of them.
-/

namespace VG.Impl.MlDsa.AArch64.KeyGen

open VG.AArch64

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-- Where the caller's `x24`–`x28` and `x30` are saved in `scratch`. -/
def SV : Nat := 840

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.x28, off)

/-! ## Moves -/

/-- `d ← v`: a `movz`, or for `v ≥ 2¹⁶` a `movz` and three `movk`s. -/
def movV (d : Reg) (v : Nat) : List Instr :=
  if v < 65536 then [.movz .x d (BitVec.ofNat 16 v) 0] else Impl.MlKem.AArch64.movImm d (BitVec.ofNat 64 v)

/-- `d ← b + off` (for `d ≠ b`). -/
def lea (d b : Reg) (off : Nat) : List Instr :=
  if off < 4096 then [.addImm .x d b off] else movV d off ++ [.add .x d b d]

/-- An argument: a pointer, or an integer (an immediate). -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- `d ← a`. -/
def Arg.instrs (d : Reg) : Arg → List Instr
  | .ptr p => lea d p.1 p.2
  | .imm v => movV d v

/-- The moves of the arguments `as` into their registers. -/
def glue : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.instrs d ++ glue as

/-- The moves of the arguments, then a call. -/
def callAt (name : String) (c : Prog isa) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (glue as)) (.call name c)

/-- The byte `v` to `p` (`p.2 < 4096`). -/
def setB (p : Ptr) (v : Nat) : List Instr := [.movz .x .x9 (BitVec.ofNat 16 v) 0, .strb .x9 p.1 p.2]

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## The primitives -/

/-- The code of the primitives `vg_mldsa_*` that key generation and
verification call. -/
structure Prims where
  suffix : String := ""
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  add : Prog isa
  sub : Prog isa
  rejNtt : Prog isa
  rejBounded : Prog isa
  ball : Prog isa
  power2Round : Prog isa
  useHint : Prog isa
  normLt : Prog isa
  simpleBitPack : Prog isa
  bitPack : Prog isa
  bitUnpack : Prog isa
  unpackT1 : Prog isa
  hintUnpack : Prog isa

section
variable (P : Prims) (ss : Ptr)

/-- `NTT(f)` in place, with the working space `ss`. -/
def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.x0, .ptr f), (.x1, .ptr ss)]

def invNttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_inv_ntt" P.invNtt [(.x0, .ptr f), (.x1, .ptr ss)]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

def addAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_add" P.add [(.x0, .ptr f), (.x1, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.x0, .ptr f), (.x1, .ptr g)]

def rejNttAt (seed a : Ptr) : Prog isa :=
  callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNtt [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

def rejBoundedAt (seed : Ptr) (eta : Nat) (a : Ptr) : Prog isa :=
  callAt ("vg_mldsa_rej_bounded_poly" ++ P.suffix) P.rejBounded
    [(.x0, .ptr seed), (.x1, .imm eta), (.x2, .ptr a), (.x3, .ptr ss)]

def ballAt (ct : Ptr) (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt ("vg_mldsa_sample_in_ball" ++ P.suffix) P.ball
    [(.x0, .ptr ct), (.x1, .imm len), (.x2, .imm tau), (.x3, .ptr c), (.x4, .ptr ss)]

def power2RoundAt (t t1 t0 : Ptr) : Prog isa :=
  callAt "vg_mldsa_power2round" P.power2Round [(.x0, .ptr t), (.x1, .ptr t1), (.x2, .ptr t0)]

def useHintAt (h r : Ptr) (g2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_use_hint" P.useHint [(.x0, .ptr h), (.x1, .ptr r), (.x2, .imm g2), (.x3, .ptr out)]

def normLtAt (f : Ptr) (bound : Nat) : Prog isa :=
  callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm bound)]

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack
    [(.x0, .ptr f), (.x1, .imm b), (.x2, .ptr out), (.x3, .imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_bit_pack" P.bitPack
    [(.x0, .ptr f), (.x1, .imm a), (.x2, .imm b), (.x3, .ptr out), (.x4, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.x0, .ptr v), (.x1, .imm len), (.x2, .imm a), (.x3, .imm b), (.x4, .ptr f)]

def unpackT1At (v f : Ptr) : Prog isa :=
  callAt "vg_mldsa_unpack_t1" P.unpackT1 [(.x0, .ptr v), (.x1, .ptr f)]

def hintUnpackAt (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_unpack" P.hintUnpack
    [(.x0, .ptr y), (.x1, .imm len), (.x2, .imm omega), (.x3, .ptr h), (.x4, .imm hlen)]

end

/-! ## Results -/

/-- `x24 ← x24 ∧ w0`, in 32 bits (a callee's `u32` result is `w0`, and the
upper half of `x0` is unspecified). -/
def and24 : List Instr := [.logic .and .w .x24 .x24 .x0]

/-- The polynomial at `a` masked by the result `w0` (0 or 1) of the sampler
that wrote it: unchanged if 1, and zero if 0, so that it is reduced either
way, without a branch. `w8 ← -w0`, then each coefficient `∧ w8`. -/
def mask (a : Ptr) : Prog isa :=
  .seq (.block ([.movz .x .x8 0 0, .sub .w .x8 .x8 .x0] ++ lea .x1 a.1 a.2 ++ [.movz .x .x2 256 0]))
    (.loop (.block [.ldr .w .x9 .x1 0, .logic .and .w .x9 .x9 .x8, .str .w .x9 .x1 0, .addImm .x .x1 .x1 4,
      .subImm .x .x2 .x2 1]) (.nonzero .x .x2))

/-- A sampler's call, its result ANDed into `x24`, and its output masked. -/
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
  .seq call (.seq (.block and24) (mask a))

/-- `c` if `x24 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := .ite (.nonzero .x .x24) c (.block [])

/-! ## The sponge -/

/-- `H` (SHAKE256) of the pieces `ins` to the pieces `outs`, with the Keccak
state at `scratch + 0` and its working space at `scratch + 200`. -/
def shake256With (c : Impl.Sha3.AArch64.Callee) (ins outs : List Impl.MlKem.AArch64.Piece) : Prog isa :=
  Impl.MlKem.AArch64.hashWith c .x28 0 200 136 0x1f ins outs

def shake256 := shake256With .scalar

/-! ## Entry and exit -/

/-- The registers saved at `scratch + SV + 8k`. -/
def savedRegs : List Reg := [.x24, .x25, .x26, .x27, .x28, .x30]

/-- Save the caller's registers in `scratch` (in `x3`), keep `scratch` in
`x28` and the other arguments in `x25`–`x27`, and `x24 ← 1`. -/
def pro : List Instr :=
  (List.range 6).map (fun k => .str .x (savedRegs.getD k .x0) .x3 (SV + 8 * k)) ++
    [.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0, .addImm .x .x28 .x3 0,
      .movz .x .x24 1 0]

/-- Return `x24` (in `x0`), and restore the caller's registers (`x28` last). -/
def epi : List Instr :=
  [.addImm .x .x0 .x24 0, .ldr .x .x30 .x28 (SV + 40), .ldr .x .x24 .x28 SV, .ldr .x .x25 .x28 (SV + 8),
    .ldr .x .x26 .x28 (SV + 16), .ldr .x .x27 .x28 (SV + 24), .ldr .x .x28 .x28 (SV + 32)]

end VG.Impl.MlDsa.AArch64.KeyGen
