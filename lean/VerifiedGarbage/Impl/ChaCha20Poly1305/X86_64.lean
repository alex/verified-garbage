import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Impl.Poly1305.X86_64

/-!
# ChaCha20-Poly1305: x86-64 implementation

`vg_chacha20_poly1305_seal(ctx = rdi, aad = rsi, aad_len = rdx, data = rcx, len = r8)`
and `vg_chacha20_poly1305_open` (the same arguments, returning `eax`), composed
of calls of the verified ChaCha20 and Poly1305 functions.

The context (1024 bytes, see `VG.Spec.ChaCha20Poly1305.sealContract`):

* `[0, 32)`: the key; `[32, 44)`: the nonce; `[48, 64)`: the tag;
* `[64, 128)`: the ChaCha20 state;
* `[128, 448)`: the working space of `vg_chacha20_xor` (the first 32 bytes of
  the block with counter 0 are the one-time Poly1305 key);
* `[448, 576)`: the Poly1305 state;
* `[576, 592)`: the padded last block of the additional data or the data;
* `[592, 632)`: our caller's `rbx, rbp, r13, r14, r15`;
* `[640, 656)`: the tag computed by `open`;
* `[656, 672)`: the lengths block.

`r15` holds the context, `r14` the data and `r13` its length, which
`vg_chacha20_xor` never writes; `rbx` and `rbp` hold the additional data and
its length, which are only needed before the call of `vg_chacha20_xor`. The
lengths block is stored before that call. After the call of
`vg_poly1305_finalize` only `rdi` (its argument, the Poly1305 state) and `rcx`
(which it returns set to its argument `out`, the tag) are used, to compare the
tags and to restore the registers.

After each call, `r15` is recomputed from a pointer argument the callee never
writes (`rsi`, into the context, for the ChaCha20 functions; `rdi` for the
Poly1305 ones). Its value does not change, but this way the constant-time
analysis knows it for the context's address, which it cannot know of a value
the callee restored from memory.

Only the pointers and the lengths can affect timing: the branches are on the
lengths, and the tags are compared without a branch.
-/

namespace VG.Impl.ChaCha20Poly1305.X86_64

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `r + d` into `d'`. -/
def ptr (d' r : Reg) (k : Nat) : List Instr := [.mov d' (.reg r), .alu .add d' (.imm (BitVec.ofNat 32 k))]

/-- The context's address into `r15`, from `r = r15 + k`. -/
def anchor (r : Reg) (k : Nat) : List Instr := [.mov .r15 (.reg r), .alu .sub .r15 (.imm (BitVec.ofNat 32 k))]

def saved : List (Reg × Nat) := [(.rbx, 592), (.rbp, 600), (.r13, 608), (.r14, 616), (.r15, 624)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rdi d) r
/-- Restores the registers, with `rdi` pointing at the Poly1305 state. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rdi (d - 448)))

/-- Where word `k` of the ChaCha20 state for counter 0 comes from: a constant
(0–3), the key (4–11), the counter (12) or the nonce (13–15). -/
def stSrc (k : Nat) : Src :=
  if k < 4 then .imm ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0)
  else if k < 12 then .mem (at_ .r15 (4 * (k - 4)))
  else if k = 12 then .imm 0
  else .mem (at_ .r15 (32 + 4 * (k - 13)))

/-- Word `k` of the ChaCha20 state, at `r15 + 64 + 4k`. -/
def stW (k : Nat) : List Instr := [.mov32 .rax (stSrc k), .store32 (at_ .r15 (64 + 4 * k)) .rax]

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Saves the registers, moves the arguments, and computes the one-time key
and the Poly1305 state for it. -/
def prologue : Prog isa :=
  .seq (.block (save ++ [.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128))
  (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
  (.seq (.block (anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128))
  (.seq (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init)
    (.block (anchor .rdi 448)))))

/-- `[rsi + rcx]` and `[r15 + rcx + 576]`. -/
def tailByte : MemOp := { base := .rsi, index := some .rcx }
def padByte : MemOp := { base := .r15, index := some .rcx, disp := 576 }

/-- The last `rdx` bytes (1 to 15) at `rsi`, padded with zeros, absorbed. -/
def padTail : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
    .mov32 .rcx (.imm 0)])
  (.seq (.loop (.block [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]) .ne)
  (.seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 576 ++ [.mov32 .rdx (.imm 1)]))
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks)
    (.block (anchor .rdi 448)))))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Reg) : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ [.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4]))
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks)
  (.seq (.block (anchor .rdi 448 ++ [.mov .rdx (.reg n), .alu .and .rdx (.imm 15)]))
    (.ite .e (.block []) (.seq (.block [.mov .rsi (.reg n), .alu .sub .rsi (.reg .rdx),
      .alu .add .rsi (.reg p)]) padTail))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted. -/
def crypt : Prog isa :=
  .seq (.block ([.mov32 .rax (.imm 1), .store32 (at_ .r15 112) .rax] ++ ptr .rdi .r15 64 ++
    [.mov .rsi (.reg .r14), .mov .rdx (.reg .r13)] ++ ptr .rcx .r15 128))
  (.seq (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor)
    (.block (anchor .rsi 128)))

/-- The lengths block. -/
def lengths : List Instr := [.store (at_ .r15 656) .rbp, .store (at_ .r15 664) .r13]

/-- The lengths block absorbed. -/
def absorbLengths : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 656 ++ [.mov32 .rdx (.imm 1)]))
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks)
    (.block (anchor .rdi 448)))

/-- The tag written to `r15 + out`: the message is whole blocks, so its
length (`count`) is 0 modulo 16, and nothing is buffered. -/
def finalizeTo (out : Nat) : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ [.mov32 .rsi (.imm 0)] ++ ptr .rdx .r15 out))
    (.call "vg_poly1305_finalize" Impl.Poly1305.X86_64.finalize)

def «seal» : Prog isa :=
  .seq prologue
  (.seq (macPad .rbx .rbp)
  (.seq (.block lengths)
  (.seq crypt
  (.seq (macPad .r14 .r13)
  (.seq absorbLengths
  (.seq (finalizeTo 48)
    (.block restore)))))))

/-- `eax = 1` if the computed tag (at `rcx`) is the received one (at
`rdi - 400`), else 0, without a branch. -/
def compare : List Instr :=
  [.mov .rax (.mem (at_ .rcx 0)), .alu .xor .rax (.mem { base := .rdi, disp := -400 }),
   .mov .rdx (.mem (at_ .rcx 8)), .alu .xor .rdx (.mem { base := .rdi, disp := -392 }),
   .alu .or .rax (.reg .rdx), .alu .cmp .rax (.imm 1), .mov32 .rax (.imm 0), .alu32 .adc .rax (.imm 0)]

def «open» : Prog isa :=
  .seq prologue
  (.seq (macPad .rbx .rbp)
  (.seq (macPad .r14 .r13)
  (.seq (.block lengths)
  (.seq absorbLengths
  (.seq crypt
  (.seq (finalizeTo 640)
    (.block (compare ++ restore))))))))

end VG.Impl.ChaCha20Poly1305.X86_64
