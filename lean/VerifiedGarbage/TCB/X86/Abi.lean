import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.Sig

/-!
# The cdecl calling convention, for `Sig`

**Trusted.** Every argument is on the stack, from `[esp + 4]` on entry
upwards: a 32-bit one in a 4-byte slot, a 64-bit one in two (low word
first), with no further alignment. The callee owns the argument area and may
overwrite it (see `Spec/Sha256/X86.lean`); the return address at `[esp]`
may not be touched. The caller's frame (at and above `esp`) does not wrap
around the end of the address space. The result is in `eax` (low word) and
`edx`.
-/

namespace VG.X86

/-- The offsets from `esp + 4` (in 4-byte slots) of arguments of widths `ws`
(32 or 64 bits). -/
def slots : List Nat → Nat → List Nat
  | [], _ => []
  | w :: ws, i => i :: slots ws (i + w / 32)

def argVal (s : State) (w i : Nat) : BitVec 64 :=
  if w = 64 then arg s (i + 1) ++ arg s i else (arg s i).setWidth 64

/-- The size in bytes of the arguments. -/
def argBytes (ws : List Nat) : Nat := 4 * (ws.map (· / 32)).sum

def abi : Abi isa where
  ptrBits := 32
  args ws := if ws.all (fun w => w = 32 ∨ w = 64) then
    some fun s => (ws.zip (slots ws 0)).map fun (w, i) => argVal s w i else none
  argArea ws s := if argBytes ws = 0 then [] else [(⟨argAddr s 0, argBytes ws⟩, true)]
  reserved s := [⟨(s.gpr .esp).setWidth 64, 4⟩]
  wf ws s := (s.gpr .esp).toNat + 4 + argBytes ws ≤ 2 ^ 32
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret _ s := s.gpr .edx ++ s.gpr .eax

end VG.X86
