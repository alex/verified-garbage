import VerifiedGarbage.Impl.MlKem.X86_64.Common
import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# ML-DSA on x86-64, signing: the pieces of the top-level function

`vg_mldsa{44,65,87}_sign` is a sequence of calls of the polynomial
primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge functions, on
buffers in its working space `scratch` (whose address it keeps in `rbx`)
and its arguments (whose addresses it keeps in `rbp`, `r12`, `r13` and
`r14`): all callee-saved registers, which the functions it calls preserve.
A buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into their registers
(`lea`, a `mov` and an `add`, and `mov`s of immediates).

The code is generic in the implementations of the primitives (`Prims`): the
proofs hold for any code that meets their contracts.
-/

namespace VG.Impl.MlDsa.X86_64.Sign

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

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
at 200 (640 bytes); the caller's callee-saved registers at 840 (48 bytes);
the iterations left (`CNT`), the counter `κ` (`KAP`) and the number of 1s
of the hint (`ONES`) at 888, 896 and 904 (8 bytes each); the seed of
`RejNTTPoly` (`RS`, 34 bytes) at 912; the seed of `ExpandMask` (`MS`,
`ρ″` and two bytes) at 960; `c̃` (`CT`, up to 64 bytes) at 1040; the
encoding of `w₁` (`W1`, up to 1024 bytes) at 2048; the working space of
the primitives (`PS`, 2048 bytes) at 3072; and polynomials of 1024 bytes
from 5120 (`P i`). -/

def oSV : Nat := 840
def oCNT : Nat := 888
def oKAP : Nat := 896
def oONES : Nat := 904
def oRS : Nat := 912
def oMS : Nat := 960
def oCT : Nat := 1040
def oW1 : Nat := 2048
def oPS : Nat := 3072
/-- Polynomial `i`. -/
def oP (i : Nat) : Nat := 5120 + 1024 * i

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.rbx, off)

/-! ## Moves -/

/-- `d ← p.1 + p.2`. -/
def lea (d : Reg) (p : Ptr) : List Instr := [.mov d (.reg p.1), .alu .add d (.imm (BitVec.ofNat 32 p.2))]

/-- `d ← v` (32 bits, zero-extended). -/
def movi (d : Reg) (v : Nat) : List Instr := [.mov32 d (.imm (BitVec.ofNat 32 v))]

/-- The byte `v` to `p`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .store8 (at_ p.1 p.2) .rax]

/-- The 8 bytes `v` to `p`. -/
def setQ (p : Ptr) (v : Nat) : List Instr := [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .store (at_ p.1 p.2) .rax]

/-- Copy `n` bytes from `src` to `dst`, one at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 n))]))
    (.loop (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-! ## Calls

A call's arguments are pointers or immediates (`Arg`), moved into the
argument registers `rdi, rsi, rdx, rcx, r8, r9` in order (`setArgs`). -/

/-- An argument: a pointer, or an immediate. -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .ptr p => lea d p
  | .imm v => movi d v

/-- The argument registers, in order. -/
abbrev argRegs6 : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- Move the arguments into their registers. -/
def setArgs (as : List Arg) : List Instr := (argRegs6.zip as).flatMap fun (d, a) => a.mov d

/-- A call of `c`, named `name`, with the arguments `as`. -/
def callP (name : String) (c : Prog isa) (as : List Arg) : Prog isa := .seq (.block (setArgs as)) (.call name c)

/-! ## The sponge -/

/-- The 25 lanes at `b + off`, zeroed (with `rax = 0`). -/
def zeroSt (b : Reg) (off : Nat) : List Instr := (List.range 25).map fun k => .store (at_ b (off + 8 * k)) .rax

/-- Zero the Keccak state. -/
def kzero : List Instr := .mov32 .rax (.imm 0) :: zeroSt .rbx 0

/-- Absorb the `len` bytes at `src`, at position `pos` of the block of `rate` bytes. -/
def kabs (src : Ptr) (len rate pos : Nat) : Prog isa :=
  callP "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb
    [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)]

/-- Pad, at position `pos`, with the suffix `suffix`. -/
def kpad (rate pos suffix : Nat) : Prog isa :=
  callP "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)]

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (rate : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  callP "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze
    [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)]

/-- Absorb the pieces `ps`, from position `pos` of the block. -/
def absAll (rate : Nat) : List (Ptr × Nat) → Nat → Prog isa
  | [], _ => .block []
  | (p, l) :: ps, pos => .seq (kabs p l rate pos) (absAll rate ps ((pos + l) % rate))

/-- The total length of the pieces. -/
def totLen (ps : List (Ptr × Nat)) : Nat := (ps.map (·.2)).sum

/-- SHAKE256 (rate 136, suffix `0x1f`) of the concatenation of the pieces
`ps`, `len` bytes of it to `out`. -/
def shakeAt (ps : List (Ptr × Nat)) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block kzero) (.seq (absAll 136 ps 0) (.seq (kpad 136 (totLen ps % 136) 0x1f) (ksqz 136 out len)))

/-! ## Sequences -/

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## The polynomial primitives

Each takes its working space (if any) at `PS`. -/

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callP "vg_mldsa_ntt" P.ntt [.ptr f, .ptr (sc oPS)]

def invNttAt (f : Ptr) : Prog isa := callP "vg_mldsa_inv_ntt" P.invNtt [.ptr f, .ptr (sc oPS)]

def mulAt (h f g : Ptr) : Prog isa := callP "vg_mldsa_multiply_ntt" P.mul [.ptr h, .ptr f, .ptr g]

def mulAddAt (h f g : Ptr) : Prog isa := callP "vg_mldsa_multiply_add_ntt" P.mulAdd [.ptr h, .ptr f, .ptr g]

def addAt (f g : Ptr) : Prog isa := callP "vg_mldsa_add" P.add [.ptr f, .ptr g]

def subAt (f g : Ptr) : Prog isa := callP "vg_mldsa_sub" P.sub [.ptr f, .ptr g]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `r15 ← r15 ∧ result`. -/
def rejAt (a : Ptr) : Prog isa :=
  .seq (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
    (.block [.alu32 .and .r15 (.reg .rax)])

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Ptr) : Prog isa :=
  callP "vg_mldsa_expand_mask_poly" P.expandMask [.ptr (sc oMS), .imm gamma1, .ptr a, .ptr (sc oPS)]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`. -/
def ballAt (len tau : Nat) (c : Ptr) : Prog isa :=
  callP "vg_mldsa_sample_in_ball" P.ball [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)]

def highBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callP "vg_mldsa_high_bits" P.highBits [.ptr r, .imm gamma2, .ptr out]

def lowBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callP "vg_mldsa_low_bits" P.lowBits [.ptr r, .imm gamma2, .ptr out]

/-- `‖f‖∞ < bound`, and `r15 ← r15 ∧ result`. -/
def normAt (f : Ptr) (bound : Nat) : Prog isa :=
  .seq (callP "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm bound]) (.block [.alu32 .and .r15 (.reg .rax)])

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s added to `ONES`. -/
def makeHintAt (z r : Ptr) (gamma2 : Nat) (h : Ptr) : Prog isa :=
  .seq (callP "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm gamma2, .ptr h])
    (.block [.mov32 .rcx (.mem (at_ .rbx oONES)), .alu32 .add .rcx (.reg .rax), .store (at_ .rbx oONES) .rcx])

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callP "vg_mldsa_simple_bit_pack" P.simpleBitPack [.ptr f, .imm b, .ptr out, .imm len]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callP "vg_mldsa_bit_pack" P.bitPack [.ptr f, .imm a, .imm b, .ptr out, .imm len]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callP "vg_mldsa_bit_unpack" P.bitUnpack [.ptr v, .imm len, .imm a, .imm b, .ptr f]

def hintBitPackAt (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : Prog isa :=
  callP "vg_mldsa_hint_bit_pack" P.hintBitPack [.ptr h, .imm hlen, .imm omega, .ptr y, .imm len]

end

/-! ## Branches, entry and exit -/

/-- `t` if `r15 ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa := .seq (.block [.alu32 .test .r15 (.reg .r15)]) (.ite .ne t e)

/-- `c` if `r15 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-- The callee-saved registers the function saves, at `scratch + 840 + 8k`. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save the callee-saved registers in the working space at `scr`, keep `scr`
in `rbx` and the pointers in the other registers (`moves`), and `r15 ← 1`. -/
def topPro (scr : Reg) (moves : List (Reg × Reg)) : List Instr :=
  (List.range 6).map (fun k => .store (at_ scr (oSV + 8 * k)) (savedRegs.getD k .rbx)) ++
    [.mov .rbx (.reg scr)] ++ moves.map (fun m => .mov m.1 (.reg m.2)) ++ [.mov32 .r15 (.imm 1)]

/-- Return `r15`, and restore the callee-saved registers (`rbx` last). -/
def topEpi : List Instr :=
  .mov32 .rax (.reg .r15) ::
    ((List.range 5).map fun k => .mov (savedRegs.getD (5 - k) .rbx) (.mem (at_ .rbx (oSV + 8 * (5 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSV))]

end VG.Impl.MlDsa.X86_64.Sign
