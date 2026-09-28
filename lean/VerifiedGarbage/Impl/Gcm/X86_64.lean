import VerifiedGarbage.TCB.X86_64.Isa

/-!
# GHASH: x86-64 implementation

`vg_ghash(h = rdi, y = rsi, data = rdx, n = rcx, scratch = r8)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 bit by bit, as `Spec.Gcm.mul` defines it:

* The blocks are big-endian: each 8-byte half is loaded with `mov` and
  `bswap`. A 128-bit value is kept in two registers, `hi` (the first eight
  bytes) and `lo`.
* `Y ⊕ X` is in `r9:r10`. Each step shifts it left by one bit
  (`add lo, lo; adc hi, hi`), which leaves its most significant bit `xᵢ`
  in CF, and `sbb m, m` turns that into the mask `m = −xᵢ`.
* `Z` (in `r11:rax`) accumulates `V & m`, so `Z := Z ⊕ V` exactly when
  `xᵢ = 1`.
* `V` (in `rbx:rbp`, starting at `H`) is shifted right by one bit; the bit
  shifted out of the low half (CF after `shr lo, 1`) becomes the mask
  `−LSB₁(V)` (`sbb`), which selects the reduction constant `R` (the high
  half `0xE1 ‖ 0⁵⁶`, in `r14`).
* The 128 steps are a loop of `unroll` steps per iteration, counted down in
  `r15`. `Y` is written back to `y` after every block.
* `rbx, rbp, r12–r15` are saved in `scratch[0..48)` and restored on exit.
* `rdi, rsi, rdx, rcx, r8` (the pointers and the block count) are public;
  no address and no branch depends on anything else.
-/

namespace VG.Impl.Gcm.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `Y ⊕ X`, shifted left one bit per step. -/
def XH : Reg := .r9
def XL : Reg := .r10
/-- The product so far, `Z`. -/
def ZH : Reg := .r11
def ZL : Reg := .rax
/-- `V`. -/
def VH : Reg := .rbx
def VL : Reg := .rbp
/-- The masks `−xᵢ` and `−LSB₁(V)`. -/
def M : Reg := .r12
/-- A temporary. -/
def T : Reg := .r13
/-- The high half of `R`. -/
def RH : Reg := .r14
/-- The loop counter. -/
def CNT : Reg := .r15

/-- The high half of `R = 11100001 ‖ 0¹²⁰` (its low half is 0). -/
def rHigh : BitVec 64 := 0xE100000000000000

/-- Steps per iteration of the inner loop. -/
def unroll : Nat := 8

/-- One step `i` of Algorithm 1. -/
def step : List Instr := [
  -- CF := xᵢ, and M := −xᵢ
  .alu .add XL (.reg XL),
  .alu .adc XH (.reg XH),
  .alu .sbb M (.reg M),
  -- Z := Z ⊕ (V ∧ M)
  .mov T (.reg VH),
  .alu .and T (.reg M),
  .alu .xor ZH (.reg T),
  .mov T (.reg VL),
  .alu .and T (.reg M),
  .alu .xor ZL (.reg T),
  -- T := LSB₁(VH) ‖ 0⁶³
  .mov T (.reg VH),
  .alu .and T (.imm 1),
  .shift .ror T 1,
  -- VL := VL >> 1 with the low bit of VH on top, M := −LSB₁(V)
  .shift .shr VL 1,
  .alu .sbb M (.reg M),
  .alu .or VL (.reg T),
  -- VH := (VH >> 1) ⊕ (R ∧ M)
  .shift .shr VH 1,
  .alu .and M (.reg RH),
  .alu .xor VH (.reg M)]

/-- `unroll` steps, then the count (setting ZF when it hits 0). -/
def steps : List Instr :=
  (List.range unroll).flatMap (fun _ => step) ++ [.alu .sub CNT (.imm 1)]

/-- Load `Y ⊕ X`, `V := H`, `Z := 0`, `R` and the count. -/
def load : List Instr := [
  .mov XH (.mem (at_ .rsi 0)), .bswap XH,
  .mov T (.mem (at_ .rdx 0)), .bswap T,
  .alu .xor XH (.reg T),
  .mov XL (.mem (at_ .rsi 8)), .bswap XL,
  .mov T (.mem (at_ .rdx 8)), .bswap T,
  .alu .xor XL (.reg T),
  .mov VH (.mem (at_ .rdi 0)), .bswap VH,
  .mov VL (.mem (at_ .rdi 8)), .bswap VL,
  .mov ZH (.imm 0), .mov ZL (.imm 0),
  .movImm64 RH rHigh,
  .mov CNT (.imm (BitVec.ofNat 32 (128 / unroll)))]

/-- Store `Z` as the new `Y`, advance to the next block and decrement the
count (setting ZF when it hits 0). -/
def store : List Instr := [
  .bswap ZH, .store (at_ .rsi 0) ZH,
  .bswap ZL, .store (at_ .rsi 8) ZL,
  .alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (.loop (.block steps) .ne) (.block store))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r8 d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r8 d))

def ghash : Prog isa :=
  .seq (.block (save ++ [.alu .test .rcx (.reg .rcx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Gcm.X86_64
