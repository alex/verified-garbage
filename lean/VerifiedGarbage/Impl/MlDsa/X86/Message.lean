import VerifiedGarbage.Impl.MlKem.X86.Basic
import VerifiedGarbage.Impl.Sha3.X86.Stream
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk, msg, msg_len, ctx, ctx_len, rnd, sig, scratch) -> eax`
and `verify_message(pk, msg, msg_len, ctx, ctx_len, sig, scratch) -> eax`,
all their arguments on the stack (cdecl): `ML-DSA.Sign` and `ML-DSA.Verify`
(FIPS 204 Algorithms 2 and 3), as calls of the sponge functions and of the
functions on `μ` (`vg_mldsa*_sign`, `vg_mldsa*_verify`), named `n` and with
the code `f`.

Each is a `leaf`: it saves its caller's `ebx`, `esi`, `edi` and `ebp` in a
frame of 16 bytes, so that its arguments are at `[esp + 20 + 4i]`. If
`ctx_len ≥ 256` it returns 2 at once. Otherwise it works in the 1 KiB after
the working space of the function on `μ` (at `oE p`, from `scratch`; its
address is kept in `esi`): the Keccak state (200 bytes), the sponge
functions' working space (640 bytes), `μ` (64 bytes), and the two bytes
`0 ‖ ctx_len` of the formatted message (at 944).

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Each call's arguments are set in its registers from the arguments on the
stack (plus an offset), offsets from `esi`, immediates, or `eax` (the
position the previous call of `vg_keccak_absorb` returned, which `callRet`
keeps), and pushed in a frame of their own. Every address and branch
depends only on the pointers and the lengths, and the calls' own leakage.
-/

namespace VG.Impl.MlDsa.X86.Message

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf callWith callRet)
open VG.Spec.MlDsa (Params)

/-- Where the 1 KiB starts in `scratch`: after the working space of the
functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-- The Keccak state, the sponge functions' working space, `μ`, and the two
bytes of the formatted message, from `esi`. -/
def oST : Nat := 0
def oKS : Nat := 200
def oMU : Nat := 840
def oHdr : Nat := 944

/-- `[esp + 20 + 4i]`: argument `i`, in the body of a leaf. -/
def argAt (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-! ## Calls -/

/-- An argument of a call. -/
inductive Arg
  /-- Argument `i` of the function. -/
  | arg (i : Nat)
  /-- Argument `i`, plus `o`. -/
  | argOff (i o : Nat)
  /-- `esi + o`. -/
  | off (o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `eax`. -/
  | ret

/-- Set `d` to the argument `a`. -/
def Arg.set (d : Reg) : Arg → List Instr
  | .arg i => [.mov d (.mem (argAt i))]
  | .argOff i o => [.mov d (.mem (argAt i)), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .off o => [.mov d (.reg .esi), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .imm v => [.mov d (.imm (BitVec.ofNat 32 v))]
  | .ret => [.mov d (.reg .eax)]

/-- Set the arguments' registers, in order. -/
def setArgs (as : List (Reg × Arg)) : List Instr := as.flatMap fun (d, a) => a.set d

/-! ## The sponge -/

/-- The registers of a call's six and five arguments, in the order pushed. -/
abbrev rs6 : List Reg := [.edi, .ebp, .ebx, .edx, .ecx, .eax]
abbrev rs5 : List Reg := [.edi, .ebx, .edx, .ecx, .eax]

/-- The Keccak state at `esi`, zeroed (through `eax`). -/
def zeroSt : List Instr := .mov .eax (.imm 0) :: (List.range 50).flatMap fun k => [.store (at_ .esi (4 * k)) .eax]

/-- Absorb `len` bytes at `src`, at the position `pos` of the block (rate
136), keeping the position it returns in `eax`. -/
def kabs (src len pos : Arg) : Prog isa :=
  .seq (.block (setArgs [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, src), (.ebp, len),
      (.edi, .off oKS)]))
    (callRet rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb)

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Arg) : Prog isa :=
  .seq (.block (setArgs [(.edx, pos), (.eax, .off oST), (.ecx, .imm 136), (.ebx, .imm 0x1f), (.edi, .off oKS)]))
    (callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad)

/-- Squeeze 64 bytes from position 0 to `μ`. -/
def ksqz : Prog isa :=
  .seq (.block (setArgs [(.eax, .off oST), (.ecx, .imm 136), (.edx, .imm 0), (.ebx, .off oMU), (.ebp, .imm 64),
      (.edi, .off oKS)]))
    (callWith rs6 "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze)

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Arg) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs tr (.imm 64) (.imm 0)) (.seq (kabs (.off oHdr) (.imm 2) (.imm 64))
    (.seq (kabs (.arg 3) (.arg 4) (.imm 66)) (.seq (kabs (.arg 1) (.arg 2) .ret)
      (.seq (kpad .ret) ksqz)))))

/-- `tr = H(pk, 64)` to the buffer of `μ`. -/
def trHash (p : Params) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs (.arg 0) (.imm p.pkLen) (.imm 0))
    (.seq (kpad (.imm (p.pkLen % 136))) ksqz))

/-! ## The functions -/

/-- `esi ← scratch + oE p`, for `scratch` argument `si`; then `0 ‖ ctx_len`
at `esi + 944`. -/
def enter (si : Nat) (p : Params) : Prog isa :=
  .seq (.block [.mov .esi (.mem (argAt si)), .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))])
    (.block [.mov .eax (.imm 0), .store8 (at_ .esi oHdr) .al, .mov .eax (.mem (argAt 4)),
      .store8 (at_ .esi (oHdr + 1)) .al])

/-- The body: if `ctx_len ≥ 256`, return 2; otherwise `enter` and `rest`. -/
def top (ent rest : Prog isa) : Prog isa :=
  leaf (.seq (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)])
    (.ite .ae (.block [.mov .eax (.imm 2)]) (.seq ent rest)))

/-- `vg_mldsa*_sign_message` for the parameter set `p`, calling the signing
function on `μ` `f`, named `n`. -/
def signMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter 7 p)
    (.seq (muHash (.argOff 0 64))
      (.seq (.block (setArgs [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6), (.edi, .arg 7)]))
        (callRet rs5 n f)))

/-- `vg_mldsa*_verify_message` for the parameter set `p`, calling the
verification function on `μ` `f`, named `n`. -/
def verifyMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter 6 p)
    (.seq (trHash p) (.seq (muHash (.off oMU))
      (.seq (.block (setArgs [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6)]))
        (callRet [.ebx, .edx, .ecx, .eax] n f))))

end VG.Impl.MlDsa.X86.Message
