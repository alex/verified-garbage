import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Impl.Poly1305.X86

/-!
# ChaCha20-Poly1305: x86 (32-bit) implementation

`vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)` and
`vg_chacha20_poly1305_open` (the same arguments, returning `eax`), cdecl: the
arguments are at `[esp + 4]`, …, `[esp + 20]`. Both are composed of calls of
the verified ChaCha20 and Poly1305 functions, as on x86-64.

The context (1024 bytes, see `VG.Spec.ChaCha20Poly1305.sealContract`):

* `[0, 32)`: the key; `[32, 44)`: the nonce; `[48, 64)`: the tag;
* `[64, 128)`: the ChaCha20 state;
* `[128, 448)`: the working space of `vg_chacha20_xor` (the first 32 bytes of
  the block with counter 0 are the one-time Poly1305 key);
* `[448, 576)`: the Poly1305 state;
* `[576, 592)`: the padded last block of the additional data or the data;
* `[592, 608)`: our caller's `ebx, esi, edi, ebp`;
* `[640, 656)`: the tag computed by `open`;
* `[656, 672)`: the lengths block.

`edi` holds the context throughout: the callees are cdecl, so they preserve
it. Every other argument is loaded from its slot on the stack when it is
needed (the stack arguments are never written). Each call pushes its
arguments in a frame of its own (`callWith`), popped into `eax` when it
returns: with its return address, a call uses at most 20 bytes below `esp`,
and `vg_chacha20_xor` 12 more below its own return address, so the functions
use 32 bytes of stack below their return address.

Only the pointers and the lengths can affect timing: the branches are on the
lengths, and the tags are compared without a branch.
-/

namespace VG.Impl.ChaCha20Poly1305.X86

open VG.X86
open VG.Impl.ChaCha20.X86 (at_)

/-- `r + k` into `d`. -/
def ptr (d r : Reg) (k : Nat) : List Instr := [.mov d (.reg r), .alu .add d (.imm (BitVec.ofNat 32 k))]

/-- Our caller's callee-saved registers, and where they are saved in the context. -/
def saved : List (Reg × Nat) := [(.ebx, 592), (.esi, 596), (.edi, 600), (.ebp, 604)]

/-- Saves them, with the context in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restores them, with the context in `edi` (restored last). -/
def restore : List Instr :=
  [.mov .ebx (.mem (at_ .edi 592)), .mov .esi (.mem (at_ .edi 596)), .mov .ebp (.mem (at_ .edi 604)),
   .mov .edi (.mem (at_ .edi 600))]

/-- A call of `name`, whose code is `body`, with the arguments `rs` pushed
(the last argument first) in a frame, popped into `eax` on return. -/
def callWith (rs : List Reg) (name : String) (body : Prog isa) : Prog isa :=
  .frame (.push rs) (.call name body) (.pop .eax rs.length)

/-- Where word `k` of the ChaCha20 state for counter 0 comes from: a constant
(0–3), the key (4–11), the counter (12) or the nonce (13–15). -/
def stSrc (k : Nat) : Src :=
  if k < 4 then .imm ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0)
  else if k < 12 then .mem (at_ .edi (4 * (k - 4)))
  else if k = 12 then .imm 0
  else .mem (at_ .edi (32 + 4 * (k - 13)))

/-- Word `k` of the ChaCha20 state, at `edi + 64 + 4k`. -/
def stW (k : Nat) : List Instr := [.mov .eax (stSrc k), .store (at_ .edi (64 + 4 * k)) .eax]

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Saves the registers, and computes the ChaCha20 state for counter 0, the
one-time key and the Poly1305 state for it. -/
def prologue : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))])
  (.seq (.block (save ++ [.mov .edi (.reg .eax)] ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128))
  (.seq (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block)
  (.seq (.block (ptr .ecx .edi 128 ++ ptr .edx .edi 448))
    (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init))))

/-- The 16 bytes at `edi + k` absorbed as one block. -/
def absorbOne (k : Nat) : Prog isa :=
  .seq (.block ([.mov .eax (.imm 1)] ++ ptr .ecx .edi k ++ ptr .edx .edi 448))
    (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks)

/-- The last `edx` bytes (1 to 15) of the `ebp` bytes at `ebx`, padded with
zeros, absorbed: they are copied (from `esi`, to `ecx`) into the zeroed
`ctx[576, 592)`. -/
def padTail : Prog isa :=
  .seq (.block ([.mov .esi (.reg .ebp), .alu .sub .esi (.reg .edx), .alu .add .esi (.reg .ebx),
    .mov .eax (.imm 0), .store (at_ .edi 576) .eax, .store (at_ .edi 580) .eax,
    .store (at_ .edi 584) .eax, .store (at_ .edi 588) .eax] ++ ptr .ecx .edi 576))
  (.seq (.loop (.block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ecx 0) .al, .alu .add .esi (.imm 1),
    .alu .add .ecx (.imm 1), .alu .sub .edx (.imm 1)]) .ne)
    (absorbOne 576))

/-- The bytes whose address and length are the stack arguments at `esp + p`
and `esp + n`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Nat) : Prog isa :=
  .seq (.block ([.mov .ebx (.mem (at_ .esp p)), .mov .ebp (.mem (at_ .esp n)), .mov .eax (.reg .ebp),
    .shift .shr .eax 4] ++ ptr .ecx .edi 448))
  (.seq (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks)
  (.seq (.block [.mov .edx (.reg .ebp), .alu .and .edx (.imm 15)])
    (.ite .e (.block []) padTail)))

/-- The lengths block. -/
def lengths : List Instr :=
  [.mov .eax (.mem (at_ .esp 12)), .store (at_ .edi 656) .eax, .mov .eax (.mem (at_ .esp 20)),
   .store (at_ .edi 664) .eax, .mov .eax (.imm 0), .store (at_ .edi 660) .eax,
   .store (at_ .edi 668) .eax]

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted. -/
def crypt : Prog isa :=
  .seq (.block ([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] ++ ptr .eax .edi 64 ++
    [.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] ++ ptr .esi .edi 128))
    (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor)

/-- The tag written to `edi + out`. -/
def finalizeTo (out : Nat) : Prog isa :=
  .seq (.block (ptr .ecx .edi out ++ [.mov .eax (.imm 0)] ++ ptr .edx .edi 656 ++ ptr .esi .edi 448))
    (callWith [.ecx, .eax, .edx, .esi] "vg_poly1305_finalize" Impl.Poly1305.X86.finalize)

def «seal» : Prog isa :=
  .seq prologue
  (.seq (macPad 8 12)
  (.seq (.block lengths)
  (.seq crypt
  (.seq (macPad 16 20)
  (.seq (absorbOne 656)
  (.seq (finalizeTo 48)
    (.block restore)))))))

/-- Word `k` of the computed tag (`edi + 640`) XORed with that of the
received one (`edi + 48`), into `r`. -/
def diff (r : Reg) (k : Nat) : List Instr :=
  [.mov r (.mem (at_ .edi (640 + 4 * k))), .alu .xor r (.mem (at_ .edi (48 + 4 * k)))]

/-- `eax = 1` if the tags are equal, else 0, without a branch: the words'
differences are ORed together, and `eax - 1` borrows if and only if that is
zero. -/
def compare : List Instr :=
  diff .eax 0 ++ diff .ecx 1 ++ [.alu .or .eax (.reg .ecx)] ++ diff .ecx 2 ++ [.alu .or .eax (.reg .ecx)] ++
  diff .ecx 3 ++ [.alu .or .eax (.reg .ecx), .alu .cmp .eax (.imm 1), .mov .eax (.imm 0),
    .alu .adc .eax (.imm 0)]

def «open» : Prog isa :=
  .seq prologue
  (.seq (macPad 8 12)
  (.seq (macPad 16 20)
  (.seq (.block lengths)
  (.seq (absorbOne 656)
  (.seq crypt
  (.seq (finalizeTo 640)
    (.block (compare ++ restore))))))))

end VG.Impl.ChaCha20Poly1305.X86
