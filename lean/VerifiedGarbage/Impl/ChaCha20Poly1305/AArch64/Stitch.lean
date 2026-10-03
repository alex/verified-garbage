import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Poly

/-!
# ChaCha20 and Poly1305 together (AArch64)

The eight-block ChaCha20 kernel (`Impl/ChaCha20/AArch64/Mixed8.lean`) keeps
the AdvSIMD units busy with six blocks and the integer units with two, one
at a time, but leaves the multiplier idle and nine general-purpose registers
free. ChaCha20-Poly1305 fills them with Poly1305 (`Poly.lean`), as
BoringSSL's `chacha20_poly1305_armv8.pl` does with its own kernel: each
chunk of 512 bytes absorbs 32 blocks of Poly1305 while its rounds run. The
two computations are independent, so out-of-order cores overlap them.

A chunk is the kernel's (`Mixed8.chunk`) with each of its two counted phases
of five double rounds replaced by `phase`: `x20` (the kernel's working space,
which the phase does not use) points at the 256 bytes the phase absorbs, a
block is absorbed, and each of the five iterations absorbs three more after
its double round; then `x20` is restored to the working space, which is 64
bytes after the ChaCha20 state in the ChaCha20-Poly1305 context.
-/

namespace VG.Impl.ChaCha20Poly1305.AArch64.Stitch

open VG.AArch64
open VG.Impl.ChaCha20.AArch64

/-- Three blocks. -/
def absorb3 : List Instr := Poly.block ++ Poly.block ++ Poly.block

/-- A counted phase with Poly1305: `start` sets `x20` to the first block. -/
def phase (sve : Bool) (start : Instr) (restore : Reg) : Prog isa :=
  .seq (.block ([start] ++ Poly.block ++ [.movz .x .x1 5 0]))
    (.seq (.loop (.seq (Mixed8.parallelRound sve) (.block (absorb3 ++ [.subImm .x .x1 .x1 1])))
        (.nonzero .x .x1))
      (.block [.addImm .x .x20 .x0 64, .addImm .x .x1 restore 0]))

/-- Where the 512 bytes a chunk absorbs start, relative to the chunk's data
(`x26` during the chunk): the chunk itself when decrypting, the previous chunk
when encrypting. -/
def start (enc : Bool) (half : Nat) : Instr :=
  if enc then .subImm .x .x20 .x26 (512 - 256 * half) else .addImm .x .x20 .x26 (256 * half)

/-- One chunk of 512 bytes, with 32 blocks of Poly1305. -/
def chunk (sve enc : Bool) : Prog isa :=
  .seq Mixed8.prepare (.seq (phase sve (start enc 0) .x26)
    (.seq Mixed8.second (.seq (phase sve (start enc 1) .x20) (.seq (Mixed8.spill 64) Mixed8.finish))))

/-- A chunk, then the counter and the pointers advanced (`Mixed8.next`). -/
def body (sve enc : Bool) : Prog isa := .seq (chunk sve enc) (.block Mixed8.next)

/-- Chunks while 512 bytes remain. -/
def chunks (sve enc : Bool) : Prog isa := .loop (body sve enc) (.zero .x .x5)

/-- The whole chunks of at least 512 bytes of data, with the stream's
registers (`x0`–`x3`, as `vg_chacha20_xor`'s arguments) and the accumulator
in `x21`–`x23`: `x19`, `x20`, `x26`, `v8` and `v9` saved in the working space
(`Mixed8.enter`), and the chunks. When encrypting, a chunk absorbs the one
before it, so the first is the kernel's own (`Mixed8.body`). -/
def bulk (sve enc : Bool) : Prog isa :=
  .seq (.block Mixed8.enter)
    (.seq (if enc then .seq (Mixed8.body sve) (.ite (.nonzero .x .x5) (.block []) (chunks sve true))
      else chunks sve false)
      (.block Mixed8.leave))

/-- The chunks that encrypt and those that decrypt, with and without SVE2, as
constants (whose literals the proofs evaluate). -/
def bulkSeal : Prog isa := bulk false true
def bulkOpen : Prog isa := bulk false false
def bulkSealSve : Prog isa := bulk true true
def bulkOpenSve : Prog isa := bulk true false

end VG.Impl.ChaCha20Poly1305.AArch64.Stitch
