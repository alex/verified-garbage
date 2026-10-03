import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# Ed448 verification on x86-64

`vg_ed448_verify(pk = rdi, context = rsi, ctxlen = rdx, message = rcx,
len = r8, signature = r9, scratch = [rsp + 8]) -> eax`: RFC 8032 §5.2.7.

If `ctxlen ≥ 256` it returns 0 at once: such a context is not an Ed448
context. Otherwise it pushes a frame of 32 words, which hold, from `rsp`:
the first ten bytes of `dom4(0, context)` (`"SigEd448" ‖ 0 ‖ ctxlen`, in two
words), the 114-byte hash, the challenge `k` (57 bytes, in eight words), and
the arguments (at the offsets `f*`). Then:

* `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame, with the sponge
  functions (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`, rate
  136, SHAKE's suffix), the Keccak state at `scratch` and their working space
  at `scratch + 256`; each absorption starts at the position the previous one
  returned (in `rax`);
* `k`, the hash reduced modulo `L` (`vg_ed448_scalar_reduce`);
* the result of `vg_ed448_verify_equation(pk, signature, k, scratch)`, kept
  in `rax` while the frame is popped into `r11`.

Each call's arguments are moved into their registers from the frame (a slot,
or a slot plus an offset), as immediates, from `rsp` plus an offset, or from
`rax`. Every address and branch depends only on the pointers and the lengths.
-/

namespace VG.Impl.Ed448.X86_64.Verify

open VG.X86_64

/-- `[rsp + d]`. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-! ## The frame -/

/-- The slots of the frame, from `rsp`. -/
def fHdr : Nat := 0
def fH : Nat := 16
def fK : Nat := 136
def fPk : Nat := 200
def fCtx : Nat := 208
def fCtxLen : Nat := 216
def fMsg : Nat := 224
def fLen : Nat := 232
def fSig : Nat := 240
def fScr : Nat := 248

/-- The registers pushed (the first at `rsp + 248`), with `scratch` in `r11`
and 0 in `rax`. -/
def regs : List Reg := [.r11, .r9, .r8, .rcx, .rdx, .rsi, .rdi] ++ List.replicate 25 .rax

/-- `"SigEd448"`, as a little-endian word. -/
def sigEd448 : Nat := 0x3834346445676953

/-- The first ten bytes of `dom4(0, context)`: `"SigEd448"`, then the word
`ctxlen · 2^8` (the bytes `0 ‖ ctxlen`, as `ctxlen < 256`), doubled eight
times in `rax`. -/
def hdr : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 sigEd448), .store (stk fHdr) .rax, .mov .rax (.mem (stk fCtxLen))] ++
    List.replicate 8 (.alu .add .rax (.reg .rax)) ++ [.store (stk (fHdr + 8)) .rax]

/-! ## Calls -/

/-- An argument of a call. -/
inductive Arg
  /-- The slot at `rsp + f`. -/
  | slot (f : Nat)
  /-- The slot at `rsp + f`, plus `o`. -/
  | slotOff (f o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `rsp + o`. -/
  | sp (o : Nat)
  /-- `rax`. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .slot f => [.mov d (.mem (stk f))]
  | .slotOff f o => [.mov d (.mem (stk f)), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .imm v => [.mov32 d (.imm (BitVec.ofNat 32 v))]
  | .sp o => [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .ret => [.mov d (.reg .rax)]

/-- The argument registers, in order. -/
abbrev argRegs6 : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- Move the arguments into their registers. -/
def setArgs (as : List Arg) : List Instr := (argRegs6.zip as).flatMap fun (d, a) => a.mov d

/-- A call of `c`, named `n`, with the arguments `as`. -/
def callA (n : String) (c : Prog isa) (as : List Arg) : Prog isa := .seq (.block (setArgs as)) (.call n c)

/-! ## The hash -/

/-- The Keccak state and the sponge functions' working space. -/
def aSt : Arg := .slot fScr
def aKs : Arg := .slotOff fScr 256

/-- The Keccak state at `scratch`, zeroed (the address, then the stores, in
blocks of their own: the stores' address is a pointer read from the frame). -/
def zeroSt : Prog isa :=
  .seq (.block [.mov .rdi (.mem (stk fScr)), .mov32 .rax (.imm 0)])
    (.block ((List.range 25).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax))

/-- Absorb `len` bytes at `src`, at the position `pos` of the block. -/
def kabs (src len pos : Arg) : Prog isa :=
  callA "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb [aSt, .imm 136, pos, src, len, aKs]

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Arg) : Prog isa :=
  callA "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad [aSt, .imm 136, pos, .imm 0x1f, aKs]

/-- Squeeze 114 bytes from position 0 into the frame. -/
def ksqz : Prog isa :=
  callA "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze [aSt, .imm 136, .imm 0, .sp fH, .imm 114, aKs]

/-- `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame at `fH`. -/
def hash : Prog isa :=
  .seq zeroSt <| .seq (kabs (.sp fHdr) (.imm 10) (.imm 0)) <| .seq (kabs (.slot fCtx) (.slot fCtxLen) .ret) <|
    .seq (kabs (.slot fSig) (.imm 57) .ret) <| .seq (kabs (.slot fPk) (.imm 57) .ret) <|
    .seq (kabs (.slot fMsg) (.slot fLen) .ret) <| .seq (kpad .ret) ksqz

/-! ## The function -/

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block hdr) <| .seq hash <|
    .seq (callA "vg_ed448_scalar_reduce" scalarReduce [.sp fK, .sp fH, .slot fScr])
      (callA "vg_ed448_verify_equation" verifyEquation [.slot fPk, .slot fSig, .sp fK, .slot fScr])

/-- `vg_ed448_verify`. -/
def verify : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 256)])
    (.ite .b (.seq (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)])
        (.frame (.push regs) body (.pop .r11 32)))
      (.block [.mov32 .rax (.imm 0)]))

end VG.Impl.Ed448.X86_64.Verify
