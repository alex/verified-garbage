import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on x86-64: `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk = rdi, msg = rsi, msg_len = rdx, ctx = rcx, ctx_len = r8,
rnd = r9, sig = [rsp + 8], scratch = [rsp + 16]) -> eax` and
`verify_message(pk = rdi, msg = rsi, msg_len = rdx, ctx = rcx, ctx_len = r8,
sig = r9, scratch = [rsp + 8]) -> eax`: `ML-DSA.Sign` and `ML-DSA.Verify`
(FIPS 204 Algorithms 2 and 3), as calls of the sponge functions and of the
functions on `μ` (`vg_mldsa*_sign`, `vg_mldsa*_verify`), named `n` and with
the code `c`.

If `ctx_len ≥ 256` they return 2 at once. Otherwise they push a frame of
nine words, which hold the arguments (at the offsets `f*`, from `rsp`) and,
at `rsp`, the two bytes `0 ‖ ctx_len` of the formatted message (the push of
a zero, then a byte store); the frame is popped into `r11`, which keeps the
result in `rax`. The 1 KiB after the working space of the function on `μ`
(at `oE p`, from `scratch`) holds the Keccak state (200 bytes), the sponge
functions' working space (640 bytes) and `μ` (64 bytes).

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Each call's arguments are moved into their registers from the frame (a slot,
or a slot plus an offset), as immediates, from `rsp` (the two bytes of the
formatted message) or from `rax` (the position the previous sponge function
returned). Every address and branch depends only on the pointers and the
lengths, and the calls' own leakage.
-/

namespace VG.Impl.MlDsa.X86_64.Message

open VG.X86_64
open VG.Spec.MlDsa (Params)

/-- `[rsp + d]`. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-! ## The frame -/

/-- The slots of the frame, from `rsp`: the two bytes of the formatted
message, `scratch`, `rnd`, `sig`, `ctx_len`, `ctx`, `msg_len`, `msg`, and
the key. -/
def fHdr : Nat := 0
def fScr : Nat := 8
def fRnd : Nat := 16
def fSig : Nat := 24
def fCtxLen : Nat := 32
def fCtx : Nat := 40
def fLen : Nat := 48
def fMsg : Nat := 56
def fKey : Nat := 64

/-- The registers signing pushes (the first at `rsp + 64`), with `sig` in
`r10`, `scratch` in `r11` and 0 in `rax`. -/
def signRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r10, .r9, .r11, .rax]

/-- The registers verification pushes, with `scratch` in `r11` and 0 in
`rax` (and an unused slot at `fRnd`). -/
def verifyRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .r11, .rax]

/-- Where the 1 KiB of the external functions starts in `scratch`: after the
working space of the functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-! ## Calls -/

/-- An argument of a call. -/
inductive Arg
  /-- The slot at `rsp + f`. -/
  | slot (f : Nat)
  /-- The slot at `rsp + f`, plus `o`. -/
  | slotOff (f o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `rsp`. -/
  | sp
  /-- `rax`. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .slot f => [.mov d (.mem (stk f))]
  | .slotOff f o => [.mov d (.mem (stk f)), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .imm v => [.mov32 d (.imm (BitVec.ofNat 32 v))]
  | .sp => [.mov d (.reg .rsp)]
  | .ret => [.mov d (.reg .rax)]

/-- The argument registers, in order. -/
abbrev argRegs6 : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- Move the arguments into their registers. -/
def setArgs (as : List Arg) : List Instr := (argRegs6.zip as).flatMap fun (d, a) => a.mov d

/-- A call of `c`, named `n`, with the arguments `as`. -/
def callA (n : String) (c : Prog isa) (as : List Arg) : Prog isa := .seq (.block (setArgs as)) (.call n c)

/-! ## The sponge -/

section
variable (p : Params)

/-- The Keccak state, the sponge functions' working space and `μ`. -/
def aSt : Arg := .slotOff fScr (oE p)
def aKs : Arg := .slotOff fScr (oE p + 200)
def aMu : Arg := .slotOff fScr (oE p + 840)

/-- The Keccak state, zeroed. -/
def zeroSt : Prog isa :=
  .seq (.block ((aSt p).mov .rdi))
    (.block (.mov32 .rax (.imm 0) :: Impl.MlDsa.X86_64.Sign.zeroSt .rdi 0))

/-- Absorb `len` bytes at `src`, at the position `pos` of the block (rate 136). -/
def kabs (src len pos : Arg) : Prog isa :=
  callA "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb [aSt p, .imm 136, pos, src, len, aKs p]

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Arg) : Prog isa :=
  callA "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad [aSt p, .imm 136, pos, .imm 0x1f, aKs p]

/-- Squeeze 64 bytes from position 0 to `μ`. -/
def ksqz : Prog isa :=
  callA "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze [aSt p, .imm 136, .imm 0, aMu p, .imm 64, aKs p]

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Arg) : Prog isa :=
  .seq (zeroSt p) (.seq (kabs p tr (.imm 64) (.imm 0)) (.seq (kabs p .sp (.imm 2) (.imm 64))
    (.seq (kabs p (.slot fCtx) (.slot fCtxLen) (.imm 66)) (.seq (kabs p (.slot fMsg) (.slot fLen) .ret)
      (.seq (kpad p .ret) (ksqz p))))))

/-- `tr = H(pk, 64)` to the buffer of `μ`. -/
def trHash : Prog isa :=
  .seq (zeroSt p) (.seq (kabs p (.slot fKey) (.imm p.pkLen) (.imm 0))
    (.seq (kpad p (.imm (p.pkLen % 136))) (ksqz p)))

end

/-! ## The functions -/

/-- The second byte of the formatted message, `ctx_len`. -/
def setHdr : List Instr := [.store8 (stk (fHdr + 1)) .r8]

/-- If `ctx_len < 256`, push the frame of `rs` (after `pre`) around `body`;
otherwise return 2. -/
def top (pre : List Instr) (rs : List Reg) (body : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 256)])
    (.ite .b (.seq (.block pre) (.frame (.push rs) (.seq (.block setHdr) body) (.pop .r11 9)))
      (.block [.mov32 .rax (.imm 2)]))

/-- `vg_mldsa*_sign_message` for the parameter set `p`, calling the signing
function on `μ` `c`, named `n`. -/
def signMessage (n : String) (c : Prog isa) (p : Params) : Prog isa :=
  top [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)] signRegs
    (.seq (muHash p (.slotOff fKey 64)) (callA n c [.slot fKey, aMu p, .slot fRnd, .slot fSig, .slot fScr]))

/-- `vg_mldsa*_verify_message` for the parameter set `p`, calling the
verification function on `μ` `c`, named `n`. -/
def verifyMessage (n : String) (c : Prog isa) (p : Params) : Prog isa :=
  top [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)] verifyRegs
    (.seq (trHash p) (.seq (muHash p (aMu p)) (callA n c [.slot fKey, aMu p, .slot fSig, .slot fScr])))

end VG.Impl.MlDsa.X86_64.Message
