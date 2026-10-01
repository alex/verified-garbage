import VerifiedGarbage.Impl.MlKem.AArch64.Sample
import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM-768 on AArch64: building blocks of the top-level functions

The top-level functions are sequences of calls of the verified primitives
and Keccak functions, on buffers at fixed offsets from pointers kept in
callee-saved registers (which the callees keep). A buffer is a register
and an offset (`Loc`); its address is computed into an argument register
(`ptrTo`), with `movz` for offsets beyond an `add`'s 12-bit immediate.

`hash` computes a SHA-3 or SHAKE function: the Keccak state (at `st` in
`scratch`) set to zero, each piece of the message absorbed in turn (each
`absorb` from the position the previous one returned), the padding, and
each piece of output squeezed in turn (likewise).
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `d ← b + off`, for `off < 65536` (and `d ≠ b`). -/
def ptrTo (d b : Reg) (off : Nat) : List Instr :=
  if off < 4096 then [.addImm .x d b off] else [.movz .x d (BitVec.ofNat 16 off) 0, .add .x d b d]

/-- A buffer: `off` bytes past the pointer in `base`, of `len` bytes. -/
structure Piece where
  base : Reg
  off : Nat
  len : Nat

/-- Zero the Keccak state at `sc + st`, through `x0` and `x9`. -/
def zeroState (sc : Reg) (st : Nat) : List Instr :=
  ptrTo .x0 sc st ++ (.movz .x .x9 0 0 :: (List.range 25).map fun k => .str .x .x9 .x0 (8 * k))

/-- The Keccak state, the rate and the working space in `x0`, `x1` and the
last argument register `wr`, and the position in `x2`: 0 at `first`, or the
position the previous call returned. -/
def keccakArgs (sc : Reg) (st wk rate : Nat) (first : Bool) (wr : Reg) : List Instr :=
  (if first then [.movz .x .x2 0 0] else [mov .x2 .x0]) ++ ptrTo .x0 sc st ++
    (.movz .x .x1 (BitVec.ofNat 16 rate) 0 :: ptrTo wr sc wk)

/-- Absorb the pieces `ps`. -/
def absorbsWith (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps =>
    .seq (.block (keccakArgs sc st wk rate first .x5 ++ ptrTo .x3 p.base p.off ++
        ([.movz .x .x4 (BitVec.ofNat 16 p.len) 0] : List Instr)))
      (.seq (.call ("vg_keccak_absorb" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)) (absorbsWith c sc st wk rate false ps))

/-- Squeeze into the pieces `ps`. -/
def squeezesWith (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate : Nat) : Bool → List Piece → Prog isa
  | _, [] => .block []
  | first, p :: ps =>
    .seq (.block (keccakArgs sc st wk rate first .x5 ++ ptrTo .x3 p.base p.off ++
        ([.movz .x .x4 (BitVec.ofNat 16 p.len) 0] : List Instr)))
      (.seq (.call ("vg_keccak_squeeze" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)) (squeezesWith c sc st wk rate false ps))

/-- The hash of the message `ins` (pieces, absorbed after one another) into
`outs`, with the rate `rate` and the domain-separation suffix `sfx`. -/
def hashWith (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate sfx : Nat) (ins outs : List Piece) : Prog isa :=
  .seq (.block (zeroState sc st)) <|
  .seq (absorbsWith c sc st wk rate true ins) <|
  .seq (.block (keccakArgs sc st wk rate false .x4 ++ ([.movz .x .x3 (BitVec.ofNat 16 sfx) 0] : List Instr)))
    (.seq (.call ("vg_keccak_pad" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c)) (squeezesWith c sc st wk rate true outs))

def absorbs := absorbsWith .scalar
def squeezes := squeezesWith .scalar
def hash := hashWith .scalar

end VG.Impl.MlKem.AArch64
