import VerifiedGarbage.Impl.MlKem.Arm.Top

/-!
# ML-DSA on 32-bit ARM, signing: the pieces of the top-level function

`vg_mldsa{44,65,87}_sign` is a sequence of calls of the polynomial
primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge functions, on
buffers in its working space `scratch` (whose address it keeps in `r7`)
and its arguments (whose addresses it keeps in `r4`, `r5`, `r6` and `r8`):
all callee-saved registers, which the functions it calls preserve. A
buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into their registers
(`movw`, `movt` and an `add` for a pointer, `movw` and `movt` for an
immediate): the first four in `r0`–`r3`, a fifth and sixth in `r12` and
`lr`, which a frame pushes around the call (`callS`), so that the callee
finds them on the stack (AAPCS). The function saved its caller's `lr`, so
it may use it.

The code is generic in the implementations of the primitives (`Prims`): the
proofs hold for any code that meets their contracts.
-/

namespace VG.Impl.MlDsa.Arm.Sign

open VG.Arm
open VG.Impl.MlKem.Arm (saveRegs copyBody absorbCall padCall squeezeCall zeroState)

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
at 200 (640 bytes); the caller's `r4`–`r11` and `lr` at 840 (36 bytes);
the iterations left (`CNT`), the counter `κ` (`KAP`) and the number of 1s
of the hint (`ONES`) at 888, 896 and 904 (4 bytes each); the seed of
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
abbrev sc (off : Nat) : Ptr := (.r7, off)

/-! ## Moves -/

/-- `d ← v` (32 bits). -/
def movi (d : Reg) (v : Nat) : List Instr := [.movw d (BitVec.ofNat 16 v), .movt d (BitVec.ofNat 16 (v / 65536))]

/-- `d ← p.1 + p.2` (`d` is not `p.1`). -/
def lea (d : Reg) (p : Ptr) : List Instr := movi d p.2 ++ [.dp .add d p.1 (.reg d)]

/-- The byte `v` (below 256) to `p`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.mov .r0 (.imm (BitVec.ofNat 32 v)), .strb .r0 p.1 p.2]

/-- The word `v` to `p`. -/
def setW (p : Ptr) (v : Nat) : List Instr := movi .r0 v ++ [.str .r0 p.1 p.2]

/-- Copy `n` bytes from `src` to `dst`, one at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .r0 src ++ lea .r1 dst ++ movi .r2 n)) (.loop (.block copyBody) .ne)

/-! ## Calls

A call's arguments are pointers or immediates (`Arg`), moved into the
argument registers `r0`–`r3`, `r12` and `lr` in order (`setArgs`). -/

/-- An argument: a pointer, or an immediate. -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .ptr p => lea d p
  | .imm v => movi d v

/-- The registers the arguments are moved into, in order. -/
abbrev argRegs6 : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

/-- Move the arguments into the registers `ds`. -/
def setArgsTo (ds : List Reg) (as : List Arg) : List Instr := (ds.zip as).flatMap fun (d, a) => a.mov d

/-- Move the arguments into their registers. -/
def setArgs (as : List Arg) : List Instr := setArgsTo argRegs6 as

/-- A call of `c`, named `name`, with the (at most four) arguments `as`, in registers. -/
def callR (name : String) (c : Prog isa) (as : List Arg) : Prog isa := .seq (.block (setArgs as)) (.call name c)

/-- A call of `c`, named `name`, with the (five or six) arguments `as`: the
fifth and sixth (in `r12` and `lr`) pushed on the stack in a frame. -/
def callS (name : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (setArgs as)) (.frame (.push [.r12, .lr]) (.call name c) (.pop .r12 8))

/-! ## The sponge -/

/-- Zero the Keccak state. -/
def kzero : List Instr := zeroState .r7

/-- Absorb the `len` bytes at `src`, at position `pos` of the block of `rate` bytes. -/
def kabs (src : Ptr) (len rate pos : Nat) : Prog isa :=
  .seq (.block (setArgs [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)])) absorbCall

/-- Pad, at position `pos`, with the suffix `suffix` (the working space in `lr`). -/
def kpad (rate pos suffix : Nat) : Prog isa :=
  .seq (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr] [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)]))
    padCall

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (rate : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (setArgs [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)])) squeezeCall

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

def nttAt (f : Ptr) : Prog isa := callR "vg_mldsa_ntt" P.ntt [.ptr f, .ptr (sc oPS)]

def invNttAt (f : Ptr) : Prog isa := callR "vg_mldsa_inv_ntt" P.invNtt [.ptr f, .ptr (sc oPS)]

def mulAt (h f g : Ptr) : Prog isa := callR "vg_mldsa_multiply_ntt" P.mul [.ptr h, .ptr f, .ptr g]

def mulAddAt (h f g : Ptr) : Prog isa := callR "vg_mldsa_multiply_add_ntt" P.mulAdd [.ptr h, .ptr f, .ptr g]

def addAt (f g : Ptr) : Prog isa := callR "vg_mldsa_add" P.add [.ptr f, .ptr g]

def subAt (f g : Ptr) : Prog isa := callR "vg_mldsa_sub" P.sub [.ptr f, .ptr g]

/-- `RejNTTPoly` of the seed at `RS` to `a`, and `r11 ← r11 ∧ result`. -/
def rejAt (a : Ptr) : Prog isa :=
  .seq (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
    (.block [.dp .and .r11 .r11 (.reg .r0)])

/-- A polynomial of `ExpandMask` from the seed at `MS` to `a`. -/
def maskAt (gamma1 : Nat) (a : Ptr) : Prog isa :=
  callR "vg_mldsa_expand_mask_poly" P.expandMask [.ptr (sc oMS), .imm gamma1, .ptr a, .ptr (sc oPS)]

/-- `SampleInBall` of the `len` bytes at `CT` to `c`. -/
def ballAt (len tau : Nat) (c : Ptr) : Prog isa :=
  callS "vg_mldsa_sample_in_ball" P.ball [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)]

def highBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callR "vg_mldsa_high_bits" P.highBits [.ptr r, .imm gamma2, .ptr out]

def lowBitsAt (r : Ptr) (gamma2 : Nat) (out : Ptr) : Prog isa :=
  callR "vg_mldsa_low_bits" P.lowBits [.ptr r, .imm gamma2, .ptr out]

/-- `‖f‖∞ < bound`, and `r11 ← r11 ∧ result`. -/
def normAt (f : Ptr) (bound : Nat) : Prog isa :=
  .seq (callR "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm bound]) (.block [.dp .and .r11 .r11 (.reg .r0)])

/-- `MakeHint` of `z` and `r` to `h`, and the number of 1s added to `ONES`. -/
def makeHintAt (z r : Ptr) (gamma2 : Nat) (h : Ptr) : Prog isa :=
  .seq (callR "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm gamma2, .ptr h])
    (.block [.ldr .r1 .r7 oONES, .dp .add .r1 .r1 (.reg .r0), .str .r1 .r7 oONES])

def simpleBitPackAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callR "vg_mldsa_simple_bit_pack" P.simpleBitPack [.ptr f, .imm b, .ptr out, .imm len]

def bitPackAt (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callS "vg_mldsa_bit_pack" P.bitPack [.ptr f, .imm a, .imm b, .ptr out, .imm len]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callS "vg_mldsa_bit_unpack" P.bitUnpack [.ptr v, .imm len, .imm a, .imm b, .ptr f]

def hintBitPackAt (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : Prog isa :=
  callS "vg_mldsa_hint_bit_pack" P.hintBitPack [.ptr h, .imm hlen, .imm omega, .ptr y, .imm len]

end

/-! ## Branches, entry and exit -/

/-- `t` if `r11 ≠ 0`, and `e` otherwise. -/
def ifOkElse (t e : Prog isa) : Prog isa := .seq (.block [.cmp .r11 (.imm 0)]) (.ite .ne t e)

/-- `c` if `r11 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa := ifOkElse c (.block [])

/-- Load `scratch` (the fifth argument, on the stack) into `r12`, save the
caller's `r4`–`r11` and `lr` at `scratch + 840`, keep `scratch` in `r7` and
the pointers in `r4`, `r5`, `r6` and `r8` (from `r0`–`r3`), and `r11 ← 1`. -/
def pro : List Instr :=
  [.ldrSp .r12 0] ++ saveRegs .r12 oSV ++
    [.str .lr .r12 (oSV + 32), .mov .r7 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .mov .r11 (.imm 1)]

end VG.Impl.MlDsa.Arm.Sign
