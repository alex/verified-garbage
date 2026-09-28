import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# AES with AES-NI on x86-64: key expansion and GCM's counter mode

Two functions, for CPUs with AES-NI (and SSSE3, for `pshufb`):

* `vg_aes_expand_key_aesni(key = rdi, key_len = rsi, schedule = rdx, scratch = rcx)`,
  with the contract of `vg_aes_expand_key` (`Spec.Aes.expandKeyContract`).
* `vg_aes_ctr32_aesni(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8,
  scratch = r9)`, with the contract of `vg_aes_ctr32` (`Spec.Gcm.ctr32Contract`).

Neither uses `scratch` or writes a callee-saved register. Every branch and
every address depends only on the pointers and the public lengths
(`key_len`, `rounds`, `n`).

## Key expansion

The schedule is computed four words (one SSE register) at a time, with
`aeskeygenassist` for `SubWord` (and `RotWord`, and the round constant,
which is an immediate: the code for each key length is straight-line). A
word `w[i]` is doubleword `i mod 4` of a register, so the register's 16
bytes in memory order are four consecutive words of the schedule as FIPS
197 lays them out, and each group of words is stored as soon as it is
computed:

* `Nk = 4`: `A = w[4k … 4k+3]`; `A' = prefixXor(A) ⊕ bcast(RotWord(SubWord(a₃)) ⊕ Rcon)`.
* `Nk = 8`: `A = w[8k … 8k+3]`, `B = w[8k+4 … 8k+7]`; `A'` as above from `b₃`,
  `B' = prefixXor(B) ⊕ bcast(SubWord(a'₃))`.
* `Nk = 6`: `A = w[6k … 6k+3]`, `B = w[6k+4], w[6k+5]` (its upper two words
  are junk); `A'` as above from `b₁`, `B' = [b₀, b₀ ⊕ b₁] ⊕ bcast(a'₃)`. `B`
  is stored as 16 bytes, of which the upper 8 are overwritten by the next `A`
  (or lie past the schedule's `16 (Nr + 1)` bytes, in the rest of the
  240-byte buffer).

`prefixXor(x)` is `[x₀, x₀ ⊕ x₁, x₀ ⊕ x₁ ⊕ x₂, x₀ ⊕ x₁ ⊕ x₂ ⊕ x₃]`, three
`pslldq`/`pxor` pairs.

## Counter mode

The counter block is kept big-endian as a GCM block (`pshufb` with a
byte-reversal mask turns the little-endian load into the block's value), so
`inc₃₂` is `paddd` with 1; it is byte-reversed back into each AES input.
Eight blocks are encrypted at a time (`xmm0`–`xmm7`), each round key loaded
once into `xmm8` and applied to all eight, so the AES pipeline stays full;
the remaining blocks go one at a time. Rounds 1–9 are straight-line, rounds
10–13 are skipped for 10 or 12 rounds (a branch on the public `rounds`),
and `r10` points at the last round key.
-/

namespace VG.Impl.Aes.X86_64.AesNi

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## Key expansion -/

/-- The round constant `Rcon[j]`'s first byte, `x^(j−1)` (FIPS 197 §5.2). -/
def rc (j : Nat) : BitVec 8 := Nat.repeat Spec.Aes.xtimes (j - 1) 1

/-- `d ← prefixXor(d) ⊕ bcast(dword sel of aeskeygenassist(s, r))`, then
store `d` at `schedule + off`. `xmm3` and `xmm4` are temporaries. -/
def kstep (d s : XReg) (sel r : BitVec 8) (off : Nat) : List Instr :=
  [.xop (.aeskeygenassist .xmm3 s r), .xop (.pshufd .xmm3 .xmm3 sel),
   .xop (.bin .movdqa .xmm4 d),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor d .xmm4),
   .xop (.bin .pxor d .xmm3),
   .movdquStore (at_ .rdx off) d]

/-- For `Nk = 6`: `B ← [b₀, b₀ ⊕ b₁, …] ⊕ bcast(a₃)` (`A` in `xmm1`, `B` in
`xmm2`), then store `B` at `schedule + off`. -/
def kstepB6 (off : Nat) : List Instr :=
  [.xop (.pshufd .xmm3 .xmm1 0xff), .xop (.bin .movdqa .xmm4 .xmm2),
   .xop (.shift .pslldq .xmm4 4), .xop (.bin .pxor .xmm2 .xmm4),
   .xop (.bin .pxor .xmm2 .xmm3),
   .movdquStore (at_ .rdx off) .xmm2]

/-- AES-128: 11 round keys. -/
def expand128 : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .movdquStore (at_ .rdx 0) .xmm1] ++
  (List.range 10).flatMap fun k => kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1))

/-- AES-192: 13 round keys (52 words), 6 words at a time. -/
def expand192 : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .movdquLoad .xmm2 (at_ .rdi 8), .xop (.shift .psrldq .xmm2 8),
   .movdquStore (at_ .rdx 0) .xmm1, .movdquStore (at_ .rdx 16) .xmm2] ++
  (List.range 7).flatMap (fun k =>
    kstep .xmm1 .xmm2 0x55 (rc (k + 1)) (24 * (k + 1)) ++ kstepB6 (24 * (k + 1) + 16)) ++
  kstep .xmm1 .xmm2 0x55 (rc 8) 192

/-- AES-256: 15 round keys (60 words), 8 words at a time. -/
def expand256 : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .movdquLoad .xmm2 (at_ .rdi 16),
   .movdquStore (at_ .rdx 0) .xmm1, .movdquStore (at_ .rdx 16) .xmm2] ++
  (List.range 6).flatMap (fun k =>
    kstep .xmm1 .xmm2 0xff (rc (k + 1)) (32 * (k + 1)) ++
    kstep .xmm2 .xmm1 0xaa 0 (32 * (k + 1) + 16)) ++
  kstep .xmm1 .xmm2 0xff (rc 7) 224

def expandKey : Prog isa :=
  .seq (.block [.alu .cmp .rsi (.imm 24)])
    (.ite .e (.block expand192)
      (.seq (.block [.alu .cmp .rsi (.imm 32)]) (.ite .e (.block expand256) (.block expand128))))

/-! ## Counter mode -/

/-- The `pshufb` mask that reverses the 16 bytes. -/
def revMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128

/-- The 128-bit constant `c` into `x`, through `rax` and `xmm12`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .xop (.movq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .xop (.movq .xmm12 .rax),
   .xop (.bin .punpcklqdq x .xmm12)]

/-- `op b, K` for each block register `b`, after loading the round key `K`
(`xmm8`) from `a`. -/
def keyOp (regs : List XReg) (op : XBinOp) (a : MemOp) : List Instr :=
  .movdquLoad .xmm8 a :: regs.map fun b => .xop (.bin op b .xmm8)

/-- Round `j` (`1 ≤ j < Nr`) of each block. -/
def round (regs : List XReg) (j : Nat) : List Instr := keyOp regs .aesenc (at_ .rdi (16 * j))

/-- AES of each block register, with `rounds` (10, 12 or 14) in `rsi`, the
key schedule at `rdi`, and its last round key at `r10`. -/
def aes (regs : List XReg) : Prog isa :=
  .seq (.block (keyOp regs .pxor (at_ .rdi 0) ++ (List.range 9).flatMap (fun j => round regs (j + 1)) ++
      [.alu .cmp .rsi (.imm 10)]))
    (.seq
      (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13)))))
      (.block (keyOp regs .aesenclast (at_ .r10 0))))

/-- The counter blocks: each block register gets the counter (`xmm9`),
byte-reversed, and the counter is incremented (`inc₃₂`). -/
def ctrs : List XReg → List Instr
  | [] => []
  | b :: bs => [.xop (.bin .movdqa b .xmm9), .xop (.bin .pshufb b .xmm10),
      .xop (.bin .paddd .xmm9 .xmm11)] ++ ctrs bs

/-- XOR block register `i` into the data block `rcx + 16 (j + i)`. -/
def xorData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.movdquLoad .xmm8 (at_ .rcx (16 * j)), .xop (.bin .pxor b .xmm8),
      .movdquStore (at_ .rcx (16 * j)) b] ++ xorData bs (j + 1)

def regs8 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

/-- Eight blocks. -/
def body8 : Prog isa :=
  .seq (.block (ctrs regs8))
    (.seq (aes regs8)
      (.block (xorData regs8 0 ++ [.alu .add .rcx (.imm 128), .alu .sub .r8 (.imm 8),
        .alu .cmp .r8 (.imm 8)])))

/-- One block. -/
def body1 : Prog isa :=
  .seq (.block (ctrs [.xmm0]))
    (.seq (aes [.xmm0])
      (.block (xorData [.xmm0] 0 ++ [.alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)])))

def ctrLoad : List Instr :=
  const .xmm10 revMask ++
  [.movImm64 .rax 1, .xop (.movq .xmm11 .rax),
   .movdquLoad .xmm9 (at_ .rdx 0), .xop (.bin .pshufb .xmm9 .xmm10),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .alu .cmp .r8 (.imm 8)]

def ctrStore : List Instr :=
  [.xop (.bin .pshufb .xmm9 .xmm10), .movdquStore (at_ .rdx 0) .xmm9]

def ctr32 : Prog isa :=
  .seq (.block ctrLoad)
    (.seq (.ite .b (.block []) (.loop body8 .ae))
      (.seq (.block [.alu .test .r8 (.reg .r8)])
        (.seq (.ite .e (.block []) (.loop body1 .ne)) (.block ctrStore))))

end VG.Impl.Aes.X86_64.AesNi
