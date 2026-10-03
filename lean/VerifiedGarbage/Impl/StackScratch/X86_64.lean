import VerifiedGarbage.TCB.X86_64.Isa

/-!
# A scratch buffer on the stack (x86-64)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack, passes the address of its
ninth byte in `r`, and runs `c` there. The frame's first eight bytes, at
`rsp`, stand for the return address that `c`'s contract keeps out of its
buffers; the buffer is the rest of the frame, which is below the stack
pointer on entry, where no Rust object lies.
-/

namespace VG.Impl.StackScratch.X86_64

open VG.X86_64

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `rsp + 8`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.mov r (.reg .rsp), .alu .add r (.imm 8)]) c) (.free bytes)

end VG.Impl.StackScratch.X86_64
