import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Impl.Sha3.AArch64.Stream

/-!
# ML-DSA on AArch64, signing: the pieces of the top-level function

`vg_mldsa{44,65,87}_sign` is a sequence of calls of the polynomial
primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge functions, on
buffers in its working space `scratch` (whose address it keeps in `x28`)
and its arguments (whose addresses it keeps in `x25`, `x26`, `x27` and
`x23`): all callee-saved registers, which the functions it calls preserve.
It keeps the AND of the results that decide whether it goes on in `x24`,
and saves its caller's values of these registers and of `x30` (the return
address, which each call overwrites) in `scratch`; it uses no stack of its
own. A buffer is at `p.1 + p.2` for a pointer `p` (a register and an
offset). Each call is preceded by the moves of its arguments into their
registers (an `add`, or a `movz` (and `movk`s) and an `add`, for a pointer;
a `movz` (and `movk`s) for an integer). The model has no flags: branches
test a register (`cbz`, `cbnz`).

The code is generic in the implementations of the primitives (`Prims`): the
proofs hold for any code that meets their contracts.
-/

namespace VG.Impl.MlDsa.AArch64.Sign

open VG.AArch64

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-- The code of the polynomial primitives that signing calls. -/
structure Prims where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  add : Prog isa
  sub : Prog isa
  rejNTT : Prog isa
  expandMask : Prog isa
  ball : Prog isa
  highBits : Prog isa
  lowBits : Prog isa
  normLt : Prog isa
  makeHint : Prog isa
  simpleBitPack : Prog isa
  bitPack : Prog isa
  bitUnpack : Prog isa
  hintBitPack : Prog isa

/-! ## The layout of the working space (in bytes)

The Keccak state at 0 (200 bytes) and the sponge functions' working space
at 200 (640 bytes); the caller's registers at 840 (56 bytes); the
iterations left (`CNT`), the counter `κ` (`KAP`) and the number of 1s of
the hint (`ONES`) at 896, 904 and 912 (8 bytes each); the seed of
`RejNTTPoly` (`RS`, 34 bytes) at 920; the seed of `ExpandMask` (`MS`,
`ρ″` and two bytes) at 960; `c̃` (`CT`, up to 64 bytes) at 1040; the
encoding of `w₁` (`W1`, up to 1024 bytes) at 2048; the working space of
the primitives (`PS`, 2048 bytes) at 3072; and polynomials of 1024 bytes
from 5120 (`P i`). -/

def oSV : Nat := 840
def oCNT : Nat := 896
def oKAP : Nat := 904
def oONES : Nat := 912
def oRS : Nat := 920
def oMS : Nat := 960
def oCT : Nat := 1040
def oW1 : Nat := 2048
def oPS : Nat := 3072
/-- Polynomial `i`. -/
def oP (i : Nat) : Nat := 5120 + 1024 * i

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.x28, off)

/-! ## Moves -/

/-- `d ← v`: a `movz`, or for `v ≥ 2¹⁶` a `movz` and three `movk`s. -/
def movV (d : Reg) (v : Nat) : List Instr :=
  if v < 65536 then [.movz .x d (BitVec.ofNat 16 v) 0] else Impl.MlKem.AArch64.movImm d (BitVec.ofNat 64 v)

/-- `d ← b + off` (for `d ≠ b`). -/
def lea (d b : Reg) (off : Nat) : List Instr :=
  if off < 4096 then [.addImm .x d b off] else movV d off ++ [.add .x d b d]

/-- The byte `v` to `p` (`p.2 < 4096`), through `x9`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.movz .x .x9 (BitVec.ofNat 16 v) 0, .strb .x9 p.1 p.2]

/-- The 8 bytes `v` to `p` (`p.2` a multiple of 8, less than 32768), through `x9`. -/
def setQ (p : Ptr) (v : Nat) : List Instr := [.movz .x .x9 (BitVec.ofNat 16 v) 0, .str .x .x9 p.1 p.2]

/-- The body of `copy`: a byte from `x1` to `x0`, both pointers advanced,
and `x2 ← x2 - 1`. -/
abbrev copyBody : List Instr :=
  [.ldrb .x9 .x1 0, .strb .x9 .x0 0, .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- Copy `n` bytes from `src` to `dst`, one at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2 ++ movV .x2 n))
    (.loop (.block copyBody) (.nonzero .x .x2))

/-! ## Calls

A call's arguments are pointers or immediates (`Arg`), each moved into its
register (`glue`). -/

/-- An argument: a pointer, or an immediate. -/
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

/-! ## The sponge -/

/-- SHAKE256 (`H`) of the concatenation of the pieces `ins`, `out.len` bytes
of it to `out`: ML-KEM's `hash` (the sponge functions' calls), with the
Keccak state at `scratch + 0` and its working space at `scratch + 200`. -/
def shakeAt (ins : List Impl.MlKem.AArch64.Piece) (out : Impl.MlKem.AArch64.Piece) : Prog isa :=
  Impl.MlKem.AArch64.hash .x28 0 200 136 0x1f ins [out]

/-! ## Sequences -/

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## The polynomial primitives

Each takes its working space (if any) at `PS`. -/

/-- `x24 ← x24 ∧ w0`, in 32 bits (a callee's `u32` result is `w0`, and the
upper half of `x0` is unspecified). -/
def and24 : List Instr := [.logic .and .w .x24 .x24 .x0]

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.x0, .ptr f), (.x1, .ptr (sc oPS))]

def invNttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_inv_ntt" P.invNtt [(.x0, .ptr f), (.x1, .ptr (sc oPS))]

def mulAt (h f g : Ptr) : Prog isa := callAt "vg_mldsa_multiply_ntt" P.mul [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa := callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

def addAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_add" P.add [(.x0, .ptr f), (.x1, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.x0, .ptr f), (.x1, .ptr g)]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `x24 ← x24 ∧ result`. -/
def rejAt (a : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_rej_ntt_poly" P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))]) (.block and24)

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_expand_mask_poly" P.expandMask [(.x0, .ptr (sc oMS)), (.x1, .imm gamma1), (.x2, .ptr a), (.x3, .ptr (sc oPS))]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`. -/
def ballAt (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball [(.x0, .ptr (sc oCT)), (.x1, .imm len), (.x2, .imm tau), (.x3, .ptr c), (.x4, .ptr (sc oPS))]

def highBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_high_bits" P.highBits [(.x0, .ptr r), (.x1, .imm gamma2), (.x2, .ptr out)]

def lowBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_low_bits" P.lowBits [(.x0, .ptr r), (.x1, .imm gamma2), (.x2, .ptr out)]

/-- `‖f‖∞ < bound`, and `x24 ← x24 ∧ result`. -/
def normAt (f : Ptr) (bound : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm bound)]) (.block and24)

/-- `ONES ← ONES + w0` (in 32 bits), through `x9`. -/
def onesAdd : List Instr := [.ldr .x .x9 .x28 oONES, .add .w .x9 .x9 .x0, .str .x .x9 .x28 oONES]

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s added to `ONES`. -/
def makeHintAt (z r : Ptr) (gamma2 : Nat) (h : Ptr) : Prog isa :=
  .seq (callAt "vg_mldsa_make_hint" P.makeHint [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm gamma2), (.x3, .ptr h)]) (.block onesAdd)

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack [(.x0, .ptr f), (.x1, .imm b), (.x2, .ptr out), (.x3, .imm len)]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_bit_pack" P.bitPack [(.x0, .ptr f), (.x1, .imm a), (.x2, .imm b), (.x3, .ptr out), (.x4, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack [(.x0, .ptr v), (.x1, .imm len), (.x2, .imm a), (.x3, .imm b), (.x4, .ptr f)]

def hintBitPackAt (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_pack" P.hintBitPack [(.x0, .ptr h), (.x1, .imm hlen), (.x2, .imm omega), (.x3, .ptr y), (.x4, .imm len)]

end

/-! ## Branches, entry and exit -/

/-- `t` if `w24 ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa := .ite (.nonzero .w .x24) t e

/-- `c` if `w24 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-- The registers the function saves, at `scratch + 840 + 8k` (`x28` last). -/
def savedRegs : List Reg := [.x23, .x24, .x25, .x26, .x27, .x30, .x28]

/-- Save the caller's registers in the working space (in `x4`), keep its
address in `x28` and the other pointers in `x25`, `x26`, `x27` and `x23`, and
`x24 ← 1`. -/
def pro : List Instr :=
  (List.range 7).map (fun k => .str .x (savedRegs.getD k .x0) .x4 (oSV + 8 * k)) ++
    [.addImm .x .x28 .x4 0, .addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0,
      .addImm .x .x23 .x3 0, .movz .x .x24 1 0]

/-- Return `x24` (in `x0`), and restore the caller's registers (`x28` last). -/
def epi : List Instr :=
  .addImm .x .x0 .x24 0 :: (List.range 7).map fun k => .ldr .x (savedRegs.getD k .x0) .x28 (oSV + 8 * k)

end VG.Impl.MlDsa.AArch64.Sign
