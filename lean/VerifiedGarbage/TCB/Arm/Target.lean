import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The 32-bit ARM target (AAPCS)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for `target_arch = "arm"`. The model is of ARMv7-A: on an older
architecture version the assembler rejects instructions such as `movw`.

AAPCS (Arm's "Procedure Call Standard for the Arm Architecture"): integer and
pointer arguments arrive in `r0`–`r3`; `r4`–`r11` and `sp` are callee-saved.
A 64-bit argument takes an even-odd register pair (`r0:r1` or `r2:r3`, the
low word in the even register), skipping a register if needed; once the
registers are used up, the remaining arguments are on the stack, each
4-byte one in a 4-byte slot, the first at `[sp]` on entry (AAPCS §6.5,
stage C). The caller removes them.
The printer ends every function with `bx lr`, which returns to the address
in the link register `lr`, so `lr` must be unchanged on exit.

Not modelled: the floating-point and SIMD registers (never modified; `d8`–
`d15` are callee-saved), the flags other than N, Z, C, V (never modified), and
memory below `sp` (never granted to a function).
-/

namespace VG.Arm

def preserved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

/-- AAPCS argument registers, in order. -/
def argRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The address of the `i`-th (from 0) 4-byte argument on the stack, on entry. -/
def stackArgAddr (s : State) (i : Nat) : Addr := State.addr (s.sp + BitVec.ofNat 32 (4 * i))

/-- The value of the `i`-th (from 0) 4-byte argument on the stack, on entry. -/
def stackArg (s : State) (i : Nat) : BitVec 32 := s.mem.readW (stackArgAddr s i) 32

/-! ## The calling convention, for `Sig`

AAPCS §6.5 stage C, for integer and pointer arguments (the only ones `Sig`
has): a 32-bit argument takes the next core register of `r0`–`r3` (C.4) or,
once they are used up, the next 4-byte stack slot (C.6, C.8); a 64-bit
argument, which needs double-word alignment, takes the next even-odd register
pair, low word in the even register (C.3, C.4), or, if none is left, the next
8 bytes of stack aligned to 8 (C.6–C.8), after which no argument goes in a
register (C.6 sets NCRN to 4). Such an argument is never split between
registers and stack (C.5 needs NCRN < 4 after C.3 has made it even). The
stack arguments start at `sp` on entry (A.3). §6.5 lets the callee modify
them; `abi` only grants reading them. The caller's frame (at and above `sp`)
does not wrap around the end of the address space. A 64-bit result is
returned in `r0` (low word) and `r1`, a 32-bit one in `r0` (§6.4).
-/

/-- Where AAPCS passes an integer argument. -/
inductive Loc
  | reg (r : Reg)
  /-- A 64-bit argument in a register pair. -/
  | pair (lo hi : Reg)
  /-- A 32- or 64-bit argument at this offset from `sp`. -/
  | stack (off : Nat) (bits : Nat)
  deriving DecidableEq, Repr

/-- The locations of arguments of widths `ws` (32 or 64 bits), given the
next core register number `ncrn` and next stacked argument offset `nsaa`;
and the final `nsaa` (the size of the stack arguments). -/
def classify : List Nat → Nat → Nat → List Loc × Nat
  | [], _, nsaa => ([], nsaa)
  | w :: ws, ncrn, nsaa =>
    if w = 64 then
      let n := ncrn + ncrn % 2
      match argRegs[n]?, argRegs[n + 1]? with
      | some lo, some hi => let r := classify ws (n + 2) nsaa; (.pair lo hi :: r.1, r.2)
      | _, _ =>
        let off := (nsaa + 7) / 8 * 8
        let r := classify ws argRegs.length (off + 8); (.stack off 64 :: r.1, r.2)
    else
      match argRegs[ncrn]? with
      | some r => let r' := classify ws (ncrn + 1) nsaa; (.reg r :: r'.1, r'.2)
      | none => let r := classify ws argRegs.length (nsaa + 4); (.stack nsaa 32 :: r.1, r.2)

/-- The value of an argument, zero-extended to 64 bits. -/
def Loc.val (s : State) : Loc → BitVec 64
  | .reg r => (s.gpr r).setWidth 64
  | .pair lo hi => s.gpr hi ++ s.gpr lo
  | .stack off 64 => stackArg s (off / 4 + 1) ++ stackArg s (off / 4)
  | .stack off _ => (stackArg s (off / 4)).setWidth 64

def abi : Abi isa where
  ptrBits := 32
  args ws := if ws.all (fun w => w = 32 ∨ w = 64) then
    some fun s => (classify ws 0 0).1.map (Loc.val s) else none
  argArea ws s := let n := (classify ws 0 0).2
    if n = 0 then [] else [(⟨stackArgAddr s 0, n⟩, false)]
  reserved _ := []
  wf ws s := s.sp.toNat + (classify ws 0 0).2 ≤ 2 ^ 32
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .r1 ++ s.gpr .r0

abbrev target : Target where
  name := "arm"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"arm\""
  rustAbi := "C"
  abi := abi

end VG.Arm
