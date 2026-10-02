import VerifiedGarbage.Impl.MlKem.Arm.Sample
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa{44,65,87}_sign_message` and `_verify_message`

`sign_message(sk = r0, msg = r1, msg_len = r2, ctx = r3, ctx_len = [sp],
rnd = [sp, #4], sig = [sp, #8], scratch = [sp, #12]) -> r0` and
`verify_message(pk = r0, msg = r1, msg_len = r2, ctx = r3, ctx_len = [sp],
sig = [sp, #4], scratch = [sp, #8]) -> r0`: `ML-DSA.Sign` and
`ML-DSA.Verify` (FIPS 204 Algorithms 2 and 3), as calls of the sponge
functions and of the functions on `μ` (`vg_mldsa*_sign`,
`vg_mldsa*_verify`), named `n` and with the code `f`.

If `ctx_len ≥ 256` (`ctx_len >> 8 ≠ 0`) they return 2 at once. Otherwise
they work in the 1 KiB after the working space of the function on `μ` (at
`oE p`, from `scratch`; its address is kept in `r7`): the Keccak state (200
bytes), the sponge functions' working space (640 bytes), `μ` (64 bytes), the
caller's `r7` and `lr`, the arguments (at the offsets `f*`) and the two bytes
`0 ‖ ctx_len` of the formatted message. To compute that address they keep
the caller's `r7` for a moment in the first word of `scratch`, which the
function on `μ` overwrites later anyway.

* Signing computes `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, with `tr` the 64
  bytes of `sk` at 64, and calls `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`,
  whose fifth argument it pushes in a frame around the call.
* Verification first computes `tr = H(pk, 64)` into the buffer of `μ`, then
  `μ` from it likewise, and calls `vg_mldsa*_verify(pk, μ, sig, scratch)`.

Each call's arguments are moved into their registers from the saved
arguments (a slot, or a slot plus an offset), as offsets from `r7` or
immediates, or from `r0` (the position the previous sponge function
returned). Every address and branch depends only on the pointers and the
lengths, and the calls' own leakage.
-/

namespace VG.Impl.MlDsa.Arm.Message

open VG.Arm
open VG.Spec.MlDsa (Params)

/-- Where the 1 KiB starts in `scratch`: after the working space of the
functions on `μ`. -/
def oE (p : Params) : Nat := 8 * Spec.MlDsa.scratchWords p

/-! ## The 1 KiB, from `r7` -/

/-- The Keccak state, the sponge functions' working space and `μ`. -/
def oST : Nat := 0
def oKS : Nat := 200
def oMU : Nat := 840
/-- The caller's `r7` and `lr`. -/
def oR7 : Nat := 904
def oLR : Nat := 908
/-- The arguments: the key, `msg`, `msg_len`, `ctx`, `ctx_len`, `rnd`, `sig` and `scratch`. -/
def fKey : Nat := 912
def fMsg : Nat := 916
def fLen : Nat := 920
def fCtx : Nat := 924
def fCtxLen : Nat := 928
def fRnd : Nat := 932
def fSig : Nat := 936
def fScr : Nat := 940
/-- The two bytes of the formatted message. -/
def oHdr : Nat := 944

/-! ## Entry and exit -/

/-- The registers the entry saves, and where: the caller's `r7` (from
`r12`) and `lr`, then the arguments in `r0`–`r3`. -/
def regSaves : List (Reg × Nat) := [(.r12, oR7), (.lr, oLR), (.r0, fKey), (.r1, fMsg), (.r2, fLen), (.r3, fCtx)]

/-- Where the entry saves the arguments on the stack, from `r0`–`r3`. -/
def stkSaves : List (Reg × Nat) := [(.r0, fCtxLen), (.r1, fRnd), (.r2, fSig), (.r3, fScr)]

/-- With `scratch` at `[sp, #so]`: keep the caller's `r7` in the first word of
`scratch`, put the address of the 1 KiB in `r7`, save the caller's `r7` and
`lr` there and the arguments in `r0`–`r3`; load the arguments on the stack
into `r0`–`r3` (from the offsets `ss`) and save them; and store
`0 ‖ ctx_len`. -/
def enter (so : Nat) (p : Params) (ss : List (Reg × Nat)) : List Instr :=
  [.ldrSp .r12 so, .str .r7 .r12 0, .movw .r7 (BitVec.ofNat 16 (oE p)),
    .movt .r7 (BitVec.ofNat 16 (oE p / 65536)), .dp .add .r7 .r12 (.reg .r7), .ldr .r12 .r12 0] ++
  regSaves.map (fun a => .str a.1 .r7 a.2) ++ ss.map (fun a => .ldrSp a.1 a.2) ++
  stkSaves.map (fun a => .str a.1 .r7 a.2) ++
  [.mov .r12 (.imm 0), .strb .r12 .r7 oHdr, .strb .r0 .r7 (oHdr + 1)]

/-- Restore `lr`, then `r7`. -/
def leave : List Instr := [.ldr .lr .r7 oLR, .ldr .r7 .r7 oR7]

/-! ## Calls -/

/-- An argument of a call. -/
inductive Arg
  /-- The saved argument at `r7 + f`. -/
  | slot (f : Nat)
  /-- The saved argument at `r7 + f`, plus `o`. -/
  | slotOff (f o : Nat)
  /-- `r7 + o`. -/
  | off (o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `r0`. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .slot f => [.ldr d .r7 f]
  | .slotOff f o => [.ldr d .r7 f, .dp .add d d (.imm (BitVec.ofNat 32 o))]
  | .off o => [.movw d (BitVec.ofNat 16 o), .dp .add d .r7 (.reg d)]
  | .imm v => [.movw d (BitVec.ofNat 16 v)]
  | .ret => [.mov d (.reg .r0)]

/-- Move the arguments into their registers, in order. -/
def setArgs (as : List (Reg × Arg)) : List Instr := as.flatMap fun (d, a) => a.mov d

/-! ## The sponge -/

/-- The Keccak state, zeroed (through `r12`). -/
def zeroSt : List Instr := Impl.MlKem.Arm.zeroState .r7

/-- Absorb `len` bytes at `src`, at the position `pos` of the block (rate 136). -/
def kabs (src len pos : Arg) : Prog isa :=
  .seq (.block (setArgs [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, src), (.r12, len), (.lr, .off oKS)]))
    Impl.MlKem.Arm.absorbCall

/-- Pad at the position `pos`, with the suffix of SHAKE. -/
def kpad (pos : Arg) : Prog isa :=
  .seq (.block (setArgs [(.r2, pos), (.r0, .off oST), (.r1, .imm 136), (.r3, .imm 0x1f), (.lr, .off oKS)]))
    Impl.MlKem.Arm.padCall

/-- Squeeze 64 bytes from position 0 to `μ`. -/
def ksqz : Prog isa :=
  .seq (.block (setArgs [(.r0, .off oST), (.r1, .imm 136), (.r2, .imm 0), (.r3, .off oMU), (.r12, .imm 64),
    (.lr, .off oKS)])) Impl.MlKem.Arm.squeezeCall

/-- `μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for the 64 bytes `tr` at `tr`. -/
def muHash (tr : Arg) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs tr (.imm 64) (.imm 0)) (.seq (kabs (.off oHdr) (.imm 2) (.imm 64))
    (.seq (kabs (.slot fCtx) (.slot fCtxLen) (.imm 66)) (.seq (kabs (.slot fMsg) (.slot fLen) .ret)
      (.seq (kpad .ret) ksqz)))))

/-- `tr = H(pk, 64)` to the buffer of `μ`. -/
def trHash (p : Params) : Prog isa :=
  .seq (.block zeroSt) (.seq (kabs (.slot fKey) (.imm p.pkLen) (.imm 0))
    (.seq (kpad (.imm (p.pkLen % 136))) ksqz))

/-! ## The functions -/

/-- If `ctx_len < 256`, `enter`, `body` and `leave`; otherwise return 2. -/
def top (ent : List Instr) (body : Prog isa) : Prog isa :=
  .seq (.block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (.ite .ne (.block [.mov .r0 (.imm 2)])
      (.seq (.block ent) (.seq body (.block leave))))

/-- The loads of the arguments on the stack for signing: `ctx_len`, `rnd`,
`sig`, `scratch`. -/
def signLoads : List (Reg × Nat) := [(.r0, 0), (.r1, 4), (.r2, 8), (.r3, 12)]

/-- Those for verification (`sig` in the slot of `rnd` too). -/
def verifyLoads : List (Reg × Nat) := [(.r0, 0), (.r1, 4), (.r2, 4), (.r3, 8)]

/-- `vg_mldsa*_sign_message` for the parameter set `p`, calling the signing
function on `μ` `f`, named `n`, with its fifth argument pushed in a frame. -/
def signMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter 12 p signLoads)
    (.seq (muHash (.slotOff fKey 64))
      (.seq (.block (setArgs [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fRnd), (.r3, .slot fSig),
          (.r12, .slot fScr)]))
        (.frame (.push [.r12, .lr]) (.call n f) (.pop .r12 8))))

/-- `vg_mldsa*_verify_message` for the parameter set `p`, calling the
verification function on `μ` `f`, named `n`. -/
def verifyMessage (n : String) (f : Prog isa) (p : Params) : Prog isa :=
  top (enter 8 p verifyLoads)
    (.seq (trHash p) (.seq (muHash (.off oMU))
      (.seq (.block (setArgs [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fSig), (.r3, .slot fScr)]))
        (.call n f))))

end VG.Impl.MlDsa.Arm.Message
