import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.Sig

/-!
# The AAPCS calling convention, for `Sig`

**Trusted.** AAPCS §6.5 stage C, for integer and pointer arguments (no
floating-point ones, no aggregates): a 32-bit argument takes the next core
register of `r0`–`r3` (C.3) or, once they are used up, the next 4-byte stack
slot (C.12–C.14); a 64-bit argument takes the next even-odd register pair,
low word in the even register (C.3–C.5), or, if none is left, 8 bytes of
stack aligned to 8 (C.8–C.12), after which no argument goes in a register
(C.11: NCRN is set to 4). The stack arguments start at `sp` on entry, and
the caller's frame (at and above `sp`) does not wrap around the end of the
address space. The result is in `r0` (low word) and `r1`.
-/

namespace VG.Arm

/-- Where AAPCS passes an integer argument. -/
inductive Loc
  | reg (r : Reg)
  /-- A 64-bit argument in a register pair. -/
  | pair (lo hi : Reg)
  /-- A 32- or 64-bit argument at this offset from `sp`. -/
  | stack (off : Nat) (bits : Nat)

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
  ret _ s := s.gpr .r1 ++ s.gpr .r0

end VG.Arm
