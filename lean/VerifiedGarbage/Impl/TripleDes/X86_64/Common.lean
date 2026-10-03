import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.X86_64.Isa

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

def memOp (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }
def rr (d s : Reg) : Instr := .mov d (.reg s)
def imm (d : Reg) (n : Nat) : Instr := .mov d (.imm (BitVec.ofNat 32 n))

def shr (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.shift .shr r n]
/-- A left shift of an isolated bit, using a rotate on its zero-filled word. -/
def placeBit (r : Reg) (n : Nat) : List Instr :=
  if n = 0 then [] else [.shift .ror r (64 - n)]

/-- Rotate right by `k`, if `k` is not 0. -/
def rorBy (r : Reg) (k : Nat) : List Instr := if k = 0 then [] else [.shift .ror r k]

/-- Fixed FIPS permutation. Source and temporary are distinct from output.
Every address and instruction is independent of the input word.

The output bits that one rotation of the source brings to their places
(those of rotation `k`), and that lie in one window of 31 bits (from `w`
= 0, 31 or 62), move together: a copy of the source rotated right by
`k + w` has them in its low 31 bits, an `and` with a (sign-extended)
32-bit immediate keeps them, a rotation by `64 - w` puts them in place,
and they are XORed into the output. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n : Nat)
    (dst src tmp : Reg) : List Instr :=
  let rotOf (i : Nat) : Nat := (n - positions.getD i 1 + 64 - (m - 1 - i)) % 64
  let winOf (i : Nat) : Nat := (m - 1 - i) / 31 * 31
  [imm dst 0] ++ (List.range 64).flatMap fun k => [0, 31, 62].flatMap fun w =>
    let bits := (List.range m).filter fun i => rotOf i = k && winOf i = w
    if bits.isEmpty then [] else
    let mask := bits.foldl (fun acc i => acc ||| 2 ^ (m - 1 - i - w)) 0
    [rr tmp src] ++ rorBy tmp ((k + w) % 64) ++
      ([.alu .and tmp (.imm (BitVec.ofNat 32 mask))] : List Instr) ++ rorBy tmp ((64 - w) % 64) ++
      ([.alu .xor dst (.reg tmp)] : List Instr)

end VG.Impl.TripleDes.X86_64
