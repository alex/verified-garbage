import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on AArch64: `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk = x0, msg = x1, msg_len = x2, ctx = x3, ctx_len = x4,
rnd = x5, sig = x6, scratch = x7) -> w0` and `verify_message(pk = x0,
msg = x1, msg_len = x2, ctx = x3, ctx_len = x4, sig = x5, scratch = x6) -> w0`:
`ML-DSA.Sign` and `ML-DSA.Verify` (FIPS 204 Algorithms 2 and 3), as calls of
the sponge functions (with the Keccak permutation `c`) and of the functions
on `μ` (`vg_mldsa*_sign`, `vg_mldsa*_verify`), named `n` and with the code
`f`.

If `ctx_len ≥ 256` (`ctx_len >> 8 ≠ 0`) they return 2 at once. Otherwise
they work in the 1 KiB after the working space of the function on `μ` (at
`oE p`, from `scratch`; its address is kept in `x28`): the Keccak state
(200 bytes), the sponge functions' working space (640 bytes), `μ` (64
bytes), the caller's `x28` and `x30`, the arguments (at the offsets `f*`)
and the two bytes `0 ‖ ctx_len` of the formatted message. They use no stack
of their own.

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Each call's arguments are moved into their registers from the saved
arguments (a slot, or a slot plus an offset), as offsets from `x28` or
immediates, or from `x0` (the position the previous sponge function
returned). Every address and branch depends only on the pointers and the
lengths, and the calls' own leakage.
-/

namespace VG.Impl.MlDsa.AArch64.Message

open VG.AArch64
open VG.Spec.MlDsa (Params)

/-- Where the 1 KiB starts in `scratch`: after the working space of the
functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-! ## The 1 KiB, from `x28` -/

/-- The Keccak state, the sponge functions' working space and `μ`. -/
def oST : Nat := 0
def oKS : Nat := 200
def oMU : Nat := 840
/-- The caller's `x28` and `x30`. -/
def oX28 : Nat := 904
def oX30 : Nat := 912
/-- The arguments: the key, `msg`, `msg_len`, `ctx`, `ctx_len`, `rnd`, `sig` and `scratch`. -/
def fKey : Nat := 920
def fMsg : Nat := 928
def fLen : Nat := 936
def fCtx : Nat := 944
def fCtxLen : Nat := 952
def fRnd : Nat := 960
def fSig : Nat := 968
def fScr : Nat := 976
/-- The two bytes of the formatted message. -/
def oHdr : Nat := 984

/-! ## Entry and exit -/

/-- Save the caller's `x28` and `x30` in the 1 KiB of `scratch` (in `sr`),
keep its address in `x28`, save the arguments `as` (registers and slots),
and store `0 ‖ ctx_len`. -/
def enter (sr : Reg) (p : Params) (as : List (Reg × Nat)) : List Instr :=
  Impl.MlKem.AArch64.movImm .x9 (BitVec.ofNat 64 (oE p)) ++
    [.add .x .x9 sr .x9, .str .x .x28 .x9 oX28, .str .x .x30 .x9 oX30, .addImm .x .x28 .x9 0] ++
    as.map (fun (r, f) => .str .x r .x28 f) ++
    [.movz .x .x9 0 0, .strb .x9 .x28 oHdr, .strb .x4 .x28 (oHdr + 1)]

/-- Restore `x30`, then `x28`. -/
def leave : List Instr := [.ldr .x .x30 .x28 oX30, .ldr .x .x28 .x28 oX28]

/-! ## Calls -/

/-- An argument of a call. -/
inductive Arg
  /-- The saved argument at `x28 + f`. -/
  | slot (f : Nat)
  /-- The saved argument at `x28 + f`, plus `o`. -/
  | slotOff (f o : Nat)
  /-- `x28 + o`. -/
  | off (o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `x0`. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .slot f => [.ldr .x d .x28 f]
  | .slotOff f o => [.ldr .x d .x28 f, .addImm .x d d o]
  | .off o => [.addImm .x d .x28 o]
  | .imm v => [.movz .x d (BitVec.ofNat 16 v) 0]
  | .ret => [.addImm .x d .x0 0]

/-- Move the arguments into their registers, in order. -/
def setArgs (as : List (Reg × Arg)) : List Instr := as.flatMap fun (d, a) => a.mov d

/-- A call of `f`, named `n`, with the arguments `as`. -/
def callA (n : String) (f : Prog isa) (as : List (Reg × Arg)) : Prog isa := .seq (.block (setArgs as)) (.call n f)

/-! ## The sponge -/

section
variable (c : Impl.Sha3.AArch64.Callee)

/-- The Keccak state, zeroed (through `x0` and `x9`). -/
def zeroSt : List Instr := Impl.MlKem.AArch64.zeroState .x28 oST

/-- Absorb `len` bytes at `src`, at the position `pos` of the block (rate 136). -/
def kabs (src len pos : Arg) : Prog isa :=
  callA ("vg_keccak_absorb" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)
    [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, src), (.x4, len), (.x5, .off oKS)]

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Arg) : Prog isa :=
  callA ("vg_keccak_pad" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c)
    [(.x2, pos), (.x0, .off oST), (.x1, .imm 136), (.x3, .imm 0x1f), (.x4, .off oKS)]

/-- Squeeze 64 bytes from position 0 to `μ`. -/
def ksqz : Prog isa :=
  callA ("vg_keccak_squeeze" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)
    [(.x0, .off oST), (.x1, .imm 136), (.x2, .imm 0), (.x3, .off oMU), (.x4, .imm 64), (.x5, .off oKS)]

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Arg) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs c tr (.imm 64) (.imm 0)) (.seq (kabs c (.off oHdr) (.imm 2) (.imm 64))
    (.seq (kabs c (.slot fCtx) (.slot fCtxLen) (.imm 66)) (.seq (kabs c (.slot fMsg) (.slot fLen) .ret)
      (.seq (kpad c .ret) (ksqz c))))))

/-- `tr = H(pk, 64)` to the buffer of `μ`. -/
def trHash (p : Params) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs c (.slot fKey) (.imm p.pkLen) (.imm 0))
    (.seq (kpad c (.imm (p.pkLen % 136))) (ksqz c)))

end

/-! ## The functions -/

/-- If `ctx_len < 256`, `enter`, `body` and `leave`; otherwise return 2. -/
def top (ent : List Instr) (body : Prog isa) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x4 8])
    (.ite (.nonzero .x .x9) (.block [.movz .x .x0 2 0])
      (.seq (.block ent) (.seq body (.block leave))))

/-- The arguments signing saves. -/
def signSaves : List (Reg × Nat) :=
  [(.x0, fKey), (.x1, fMsg), (.x2, fLen), (.x3, fCtx), (.x4, fCtxLen), (.x5, fRnd), (.x6, fSig), (.x7, fScr)]

/-- The arguments verification saves (`sig` in the slot of `rnd` too). -/
def verifySaves : List (Reg × Nat) :=
  [(.x0, fKey), (.x1, fMsg), (.x2, fLen), (.x3, fCtx), (.x4, fCtxLen), (.x5, fRnd), (.x5, fSig), (.x6, fScr)]

/-- `vg_mldsa*_sign_message` for the parameter set `p`, with the Keccak
permutation `c`, calling the signing function on `μ` `f`, named `n`. -/
def signMessage (c : Impl.Sha3.AArch64.Callee) (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter .x7 p signSaves)
    (.seq (muHash c (.slotOff fKey 64))
      (callA n f [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fRnd), (.x3, .slot fSig), (.x4, .slot fScr)]))

/-- `vg_mldsa*_verify_message` for the parameter set `p`, with the Keccak
permutation `c`, calling the verification function on `μ` `f`, named `n`. -/
def verifyMessage (c : Impl.Sha3.AArch64.Callee) (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter .x6 p verifySaves)
    (.seq (trHash c p) (.seq (muHash c (.off oMU))
      (callA n f [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fSig), (.x3, .slot fScr)])))

end VG.Impl.MlDsa.AArch64.Message
