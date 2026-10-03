import VerifiedGarbage.TCB.AArch64.Isa

/-!
# A scratch buffer on the stack (AArch64)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack and passes its address in
`r`. The buffer is below the stack pointer on entry, where no Rust object
lies.
-/

namespace VG.Impl.StackScratch.AArch64

open VG.AArch64

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `sp`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 0]) c) (.free bytes)

end VG.Impl.StackScratch.AArch64
