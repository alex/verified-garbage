import VerifiedGarbage.Impl.MlKem.X86.Top

/-!
# ML-DSA on x86 (32-bit), signing: the pieces of the top-level function

`vg_mldsa{44,65,87}_sign` is a sequence of calls of the polynomial
primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge functions, on
buffers in its working space `scratch` (argument 4, whose address it keeps
in `esi`, which the functions it calls preserve) and in its other arguments
(read from the stack when needed), named as ML-KEM's top-level functions
name them (`Buf`: an argument, an offset and a length; `ptrTo`). A call
moves its arguments (addresses, `ptrTo`, and immediates) into `eax`, `ecx`,
`edx`, `ebx` and `edi`, in order, and pushes them in a frame of their own
(`callWith`, or `callRet` when it uses the value returned).

The flag `OK`, the number of iterations left `CNT`, the counter `κ` (`KAP`)
and the number of 1s of the hint (`ONES`) are words of `scratch`.

The code is generic in the implementations of the primitives (`Prims`): the
proofs hold for any code that meets their contracts.
-/

namespace VG.Impl.MlDsa.X86.Sign

open VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo callWith callRet at_ hash2 copyW)

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

/-! ## The arguments and the layout of the working space (in bytes)

The arguments are `sk` (0), `mu` (1), `rnd` (2), `sig` (3) and `scratch`
(4). In `scratch`: the Keccak state at 0 (200 bytes) and the sponge
functions' working space at 200 (640 bytes); the words `OK`, `CNT`, `KAP`
and `ONES` at 840, 844, 848 and 852; the seed of `RejNTTPoly` (`RS`, 34
bytes) at 856; `K ‖ rnd` (`HIN`, 64 bytes) at 896; the seed of
`ExpandMask` (`MS`, `ρ″` and two bytes) at 960; `c̃` (`CT`, up to 64 bytes)
at 1040; the encoding of `w₁` (`W1`, up to 1024 bytes) at 2048; the working
space of the primitives (`PS`, 2048 bytes) at 3072; and polynomials of 1024
bytes from 5120 (`P i`). -/

/-- The index of `scratch` among the arguments. -/
abbrev SC : Nat := 4

def oOK : Nat := 840
def oCNT : Nat := 844
def oKAP : Nat := 848
def oONES : Nat := 852
def oRS : Nat := 856
def oHIN : Nat := 896
def oMS : Nat := 960
def oCT : Nat := 1040
def oW1 : Nat := 2048
def oPS : Nat := 3072
def oST : Nat := 0
def oWK : Nat := 200
/-- Polynomial `i`. -/
def oP (i : Nat) : Nat := 5120 + 1024 * i

/-- `len` bytes of `scratch` at `off`. -/
abbrev sc (off len : Nat) : Buf := ⟨SC, off, len⟩

/-- The polynomial in slot `i`. -/
abbrev pS (i : Nat) : Buf := sc (oP i) 1024

/-- The working space of the primitives. -/
abbrev bPS : Buf := sc oPS 2048

/-! ## Calls

A call's arguments are addresses or immediates (`Arg`), moved into
`eax, ecx, edx, ebx, edi` in order (`setArgs`) and pushed last to first. -/

/-- An argument: the address of a buffer, or an immediate. -/
inductive Arg
  | buf (b : Buf)
  | imm (v : Nat)

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .buf b => ptrTo SC d b
  | .imm v => [.mov d (.imm (BitVec.ofNat 32 v))]

/-- The argument registers, in order. -/
abbrev argRegs : List Reg := [.eax, .ecx, .edx, .ebx, .edi]

/-- Move the arguments into their registers. -/
def setArgs : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.mov d ++ setArgs as

/-- The registers of `n` arguments, pushed last to first. -/
abbrev argPush (n : Nat) : List Reg := (argRegs.take n).reverse

/-- A call of `c`, named `name`, with the arguments `as`. -/
def callP (name : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (setArgs (argRegs.zip as))) (callWith (argPush as.length) name c)

/-- `callP`, keeping the value `c` returns in `eax`. -/
def callPR (name : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (setArgs (argRegs.zip as))) (callRet (argPush as.length) name c)

/-! ## Words and bytes of `scratch` -/

/-- The word at `o` set to `v`. -/
def st32 (o v : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax]

/-- The byte at `o` set to `v`. -/
def st8 (o v : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 v)), .store8 (at_ .esi o) .al]

/-- `OK ← OK ∧ eax`. -/
def andOK : List Instr := [.mov .ecx (.mem (at_ .esi oOK)), .alu .and .ecx (.reg .eax), .store (at_ .esi oOK) .ecx]

/-- `ONES ← ONES + eax`. -/
def addOnes : List Instr :=
  [.mov .ecx (.mem (at_ .esi oONES)), .alu .add .ecx (.reg .eax), .store (at_ .esi oONES) .ecx]

/-- `t` if `OK ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esi oOK)), .alu .test .eax (.reg .eax)]) (.ite .ne t e)

/-- `c` if `OK ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-! ## Sequences -/

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## The sponge -/

/-- SHAKE256 of the bytes of `b₁` and then `b₂`, into `o`. -/
def shake2 (b₁ b₂ o : Buf) : Prog isa := hash2 SC oST oWK 136 0x1f b₁ b₂ o

/-! ## The polynomial primitives -/

section
variable (P : Prims)

def nttAt (f : Buf) : Prog isa := callP "vg_mldsa_ntt" P.ntt [.buf f, .buf (sc oPS 1024)]

def invNttAt (f : Buf) : Prog isa := callP "vg_mldsa_inv_ntt" P.invNtt [.buf f, .buf (sc oPS 1024)]

def mulAt (h f g : Buf) : Prog isa := callP "vg_mldsa_multiply_ntt" P.mul [.buf h, .buf f, .buf g]

def mulAddAt (h f g : Buf) : Prog isa := callP "vg_mldsa_multiply_add_ntt" P.mulAdd [.buf h, .buf f, .buf g]

def addAt (f g : Buf) : Prog isa := callP "vg_mldsa_add" P.add [.buf f, .buf g]

def subAt (f g : Buf) : Prog isa := callP "vg_mldsa_sub" P.sub [.buf f, .buf g]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `OK ← OK ∧ result`. -/
def rejAt (a : Buf) : Prog isa :=
  .seq (callPR "vg_mldsa_rej_ntt_poly" P.rejNTT [.buf (sc oRS 34), .buf a, .buf bPS]) (.block andOK)

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Buf) : Prog isa :=
  callP "vg_mldsa_expand_mask_poly" P.expandMask [.buf (sc oMS 66), .imm gamma1, .buf a, .buf bPS]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`, returning its result in `eax`. -/
def ballAt (len tau : Nat) (c : Buf) : Prog isa :=
  callPR "vg_mldsa_sample_in_ball" P.ball [.buf (sc oCT len), .imm len, .imm tau, .buf c, .buf bPS]

def highBitsAt (r : Buf) (gamma2 : Nat) (out : Buf) : Prog isa :=
  callP "vg_mldsa_high_bits" P.highBits [.buf r, .imm gamma2, .buf out]

def lowBitsAt (r : Buf) (gamma2 : Nat) (out : Buf) : Prog isa :=
  callP "vg_mldsa_low_bits" P.lowBits [.buf r, .imm gamma2, .buf out]

/-- `‖f‖∞ < bound`, and `OK ← OK ∧ result`. -/
def normAt (f : Buf) (bound : Nat) : Prog isa :=
  .seq (callPR "vg_mldsa_norm_lt" P.normLt [.buf f, .imm bound]) (.block andOK)

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s added to `ONES`. -/
def makeHintAt (z r : Buf) (gamma2 : Nat) (h : Buf) : Prog isa :=
  .seq (callPR "vg_mldsa_make_hint" P.makeHint [.buf z, .buf r, .imm gamma2, .buf h]) (.block addOnes)

def simpleBitPackAt (f : Buf) (b : Nat) (out : Buf) : Prog isa :=
  callP "vg_mldsa_simple_bit_pack" P.simpleBitPack [.buf f, .imm b, .buf out, .imm out.len]

def bitPackAt (f : Buf) (a b : Nat) (out : Buf) : Prog isa :=
  callP "vg_mldsa_bit_pack" P.bitPack [.buf f, .imm a, .imm b, .buf out, .imm out.len]

def bitUnpackAt (v : Buf) (a b : Nat) (f : Buf) : Prog isa :=
  callP "vg_mldsa_bit_unpack" P.bitUnpack [.buf v, .imm v.len, .imm a, .imm b, .buf f]

def hintBitPackAt (h : Buf) (omega : Nat) (y : Buf) : Prog isa :=
  callP "vg_mldsa_hint_bit_pack" P.hintBitPack [.buf h, .imm (h.len / 4), .imm omega, .buf y, .imm y.len]

end

end VG.Impl.MlDsa.X86.Sign
