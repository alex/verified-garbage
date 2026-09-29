import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.Impl.Sha512.Arm

/-!
# Keccak-f[1600]: ARMv7 implementation

`vg_keccak_f1600(state = r0, scratch = r1)`.

The same structure as the x86-64 implementation, with each 64-bit lane a
pair of 32-bit words, the low one first (as in memory: little-endian), as in
the SHA-512 implementation (whose macros for rotations, loads and stores of
such pairs this uses: `VG.Impl.Sha512.Arm`). `scratch` (512 bytes) is laid
out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: each
  round reads one (`src`) and writes the other (`dst`), so after the 24
  rounds the result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue (built with
  `movw`/`movt`);
* `[392, 396)`: a pointer to the next round's constant;
* `[396, 432)`: the saved `r4`–`r11` and `lr`.

`r0` (`state`) and `r1` (`scratch`) are never written. The loop runs two
rounds per iteration, from `r0` to `r1` and then from `r1` to `r0`. A round
computes the five column parities `C[x]` (θ) into the register pairs
`creg x`; then `D[x]`, which it stores in the last five lanes of `dst`
(the registers do not hold both `C` and `D`); then, for each plane `y` of
the output, the five lanes `B[x]` of `π(ρ(θ(A)))` in that plane into
`creg x` (reading `D` back, before the plane's stores, so plane 4 may
overwrite it), and stores `B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, and ι for lane 0)
to `dst`, a half at a time. The model has no `bic`, so `¬b ∧ c` is computed
as `(b ∧ c) ⊕ c`. The temporaries are `r12` and `lr`.

Every address is a pointer plus a constant or the round constant pointer,
which is public, and the only branch is the round loop's, which depends
only on the pointers, so only the pointers can affect timing.
-/

namespace VG.Impl.Sha3.Arm

open VG.Arm
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Impl.Sha512.Arm (lo hi ld st Op sig)

/-- `++`, grouping to the right (see `VG.Impl.Sha512.Arm`): the kernel
evaluates the code, and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The register pair (low, high) of `C[x]`, and then of `B[x]`. -/
def cl (x : Nat) : Reg := [Reg.r2, .r4, .r6, .r8, .r10].getD x .r2
def ch (x : Nat) : Reg := [Reg.r3, .r5, .r7, .r9, .r11].getD x .r3

/-- The temporaries. -/
def T1 : Reg := .r12
def T2 : Reg := .lr

/-- The offset of `D[x]` in `dst`: its last five lanes. -/
def dOff (x : Nat) : Nat := 160 + 8 * x

/-- The offset in `scratch` of the pointer to the next round constant. -/
def rcPtr : Nat := 392

/-- `(l, h) ^= ` the lane at `[b, #off]`. -/
def ldx (l h b : Reg) (off : Nat) : List Instr :=
  [.ldr T1 b off, .dp .eor l l (.reg T1), .ldr T1 b (off + 4), .dp .eor h h (.reg T1)]

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`, from the state at `src`. -/
def column (src : Reg) (x : Nat) : List Instr :=
  ld (cl x) (ch x) src (8 * x) +++ ldx (cl x) (ch x) src (8 * (x + 5)) +++
    ldx (cl x) (ch x) src (8 * (x + 10)) +++ ldx (cl x) (ch x) src (8 * (x + 15)) +++
    ldx (cl x) (ch x) src (8 * (x + 20))

/-- `D[x] = ROTR⁶³(C[x + 1]) ⊕ C[x - 1]`, stored in `dst`. -/
def dcol (dst : Reg) (x : Nat) : List Instr :=
  sig T1 T2 (cl ((x + 1) % 5)) (ch ((x + 1) % 5)) [.rotr 63] +++
    [.dp .eor T1 T1 (.reg (cl ((x + 4) % 5))), .dp .eor T2 T2 (.reg (ch ((x + 4) % 5)))] +++
    st T1 T2 dst (dOff x)

/-- `ROTL^n` of the lane in `(T1, T2)`, into `(l, h)`, as a rotation right. -/
def rot (l h : Reg) (n : Nat) : List Instr :=
  if n = 0 then [.mov l (.reg T1), .mov h (.reg T2)] else sig l h T1 T2 [.rotr (64 - n)]

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`. -/
def laneB (src dst : Reg) (x y : Nat) : List Instr :=
  [.ldr T1 src (8 * piSrc x y), .ldr T2 dst (dOff ((x + 3 * y) % 5)), .dp .eor T1 T1 (.reg T2),
    .ldr T2 src (8 * piSrc x y + 4), .ldr (cl x) dst (dOff ((x + 3 * y) % 5) + 4),
    .dp .eor T2 T2 (.reg (cl x))] ++ rot (cl x) (ch x) (rhoOff (piSrc x y))

/-- A half of lane `(x, y)` of the output: `B[x] ⊕ ((B[x+1] ∧ B[x+2]) ⊕ B[x+2])`
in the registers `r`, and for lane 0 the half at `off` of the round
constant, stored at `[dst, #o]`. -/
def chiHalf (dst : Reg) (r : Nat → Reg) (x y off o : Nat) : List Instr :=
  [.dp .and T1 (r ((x + 1) % 5)) (.reg (r ((x + 2) % 5))),
    .dp .eor T1 T1 (.reg (r ((x + 2) % 5))), .dp .eor T1 T1 (.reg (r x))] +++
    (if x = 0 ∧ y = 0 then [.ldr T2 .r1 rcPtr, .ldr T2 T2 off, .dp .eor T1 T1 (.reg T2)] else []) +++
    [.str T1 dst o]

/-- Lane `(x, y)` of the output. -/
def chi (dst : Reg) (x y : Nat) : List Instr :=
  chiHalf dst cl x y 0 (8 * (x + 5 * y)) ++ chiHalf dst ch x y 4 (8 * (x + 5 * y) + 4)

/-- Plane `y` of the output. -/
def plane (src dst : Reg) (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB src dst x y) ++ (List.range 5).flatMap (fun x => chi dst x y)

/-- One round from `src` to `dst`; then advance to the next round constant. -/
def round (src dst : Reg) : List Instr :=
  (List.range 5).flatMap (column src) +++ (List.range 5).flatMap (dcol dst) +++
    (List.range 5).flatMap (plane src dst) +++
    [.ldr T1 .r1 rcPtr, .dp .add T1 T1 (.imm 8), .str T1 .r1 rcPtr]

/-- Two rounds, and set Z after the last. -/
def body : List Instr :=
  round .r0 .r1 +++ round .r1 .r0 +++
    [.ldr T1 .r1 rcPtr, .dp .sub T1 T1 (.reg .r1), .cmp T1 (.imm 392)]

/-- The callee-saved registers we use (and `lr`), and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 396), (.r5, 400), (.r6, 404), (.r7, 408), (.r8, 412), (.r9, 416), (.r10, 420),
    (.r11, 424), (.lr, 428)]

/-- Round constant `k`, built in `T1` and stored at `scratch + 200 + 8k`. -/
def rcStore (k : Nat) : List Instr :=
  [.movw T1 ((lo (Spec.Sha3.RC k)).extractLsb' 0 16), .movt T1 ((lo (Spec.Sha3.RC k)).extractLsb' 16 16),
    .str T1 .r1 (200 + 8 * k),
    .movw T1 ((hi (Spec.Sha3.RC k)).extractLsb' 0 16), .movt T1 ((hi (Spec.Sha3.RC k)).extractLsb' 16 16),
    .str T1 .r1 (204 + 8 * k)]

/-- Save the registers, store the round constants, and point at the first. -/
def prologue : List Instr :=
  saved.map (fun (r, d) => .str r .r1 d) +++ (List.range 24).flatMap rcStore +++
    [.dp .add T1 .r1 (.imm 200), .str T1 .r1 rcPtr]

def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

def permute : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block body) .ne) (.block restore))

end VG.Impl.Sha3.Arm
