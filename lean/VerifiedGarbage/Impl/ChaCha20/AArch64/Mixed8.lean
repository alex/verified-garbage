import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5

/-! Six row-vector blocks share execution with two integer blocks.
Each phase performs one vector double round and two integer double rounds.
Five phases finish one integer block and half of the vector rounds. -/
namespace VG.Impl.ChaCha20.AArch64.Mixed8
open VG VG.AArch64

inductive Op
  | vector (op : Rows6.Op)
  | scalar (op : Neon4.Op)

def Op.code : Op → List Instr
  | .vector op => op.code
  | .scalar op => Mixed5.scalarCode op

def interleave : List Rows6.Op → List Neon4.Op → List Op
  | [], ss => ss.map Op.scalar
  | v :: vs, [] => Op.vector v :: interleave vs []
  | v :: vs, s :: ss => Op.vector v :: Op.scalar s :: interleave vs ss

def scheduled : List Op → Prog isa
  | [] => .block []
  | op :: ops => .seq (.block op.code) (scheduled ops)

def roundOps : List Op := interleave Rows6.roundOps (Mixed5.roundOps ++ Mixed5.roundOps)
def parallelRound : Prog isa := scheduled roundOps

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) parallelRound

/-- Keep one phase in the instruction cache; x1 is free until the scalar spill. -/
def phase (restore : Reg) : Prog isa :=
  .seq (.block [.movz .x .x1 5 0])
    (.seq (.loop (.seq parallelRound (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))
      (.block [.addImm .x .x1 restore 0]))

def prepare : Prog isa := .seq (.block Mixed5.saveArgs)
  (.seq (.block Rows6.setup)
    (.seq (.block (Mixed5.counter 6)) (.block VG.Impl.ChaCha20.AArch64.load)))

def spill (offset : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x1 .x20 offset]) (.block VG.Impl.ChaCha20.AArch64.finish)

def second : Prog isa := .seq (spill 0)
  (.seq (.block (Mixed5.counter 1)) (.block VG.Impl.ChaCha20.AArch64.load))

def xorScalarRow (k : Fin 8) : List Instr :=
  [.ldrq .v30 .x3 (16 * k.val),.ldrq .v31 .x1 (384 + 16 * k.val),
   .vop (.logic .eor .v31 .v31 .v30),.strq .v31 .x1 (384 + 16 * k.val)]

def vectorFinish : Prog isa := .seq (.block Mixed5.restoreArgs)
  (.seq (.block (Mixed5.counter 7 true))
    (.block Rows6.finish))

def finish : Prog isa := .seq vectorFinish (.block ((List.finRange 8).flatMap xorScalarRow))

def chunk : Prog isa := .seq prepare (.seq (phase .x26)
  (.seq second (.seq (phase .x20) (.seq (spill 64) finish))))

def check : List Instr :=
  [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 8,.lsr .x .x5 .x5 63]

def enter : List Instr := Mixed5.enter ++ [.strq .v8 .x3 128,.strq .v9 .x3 144]
def leave : List Instr := [.ldrq .v8 .x3 128,.ldrq .v9 .x3 144] ++ Mixed5.leave

def next : List Instr := Mixed5.counter 8 ++
  [.addImm .x .x1 .x1 512,.subImm .x .x2 .x2 512] ++ check

def body : Prog isa := .seq chunk (.block next)

def xor : Prog isa := .seq (.block check)
  (.seq (.ite (.nonzero .x .x5) (.block [])
    (.seq (.block enter) (.seq (.loop body (.zero .x .x5)) (.block leave))))
    VG.Impl.ChaCha20.AArch64.Small.xor)

end VG.Impl.ChaCha20.AArch64.Mixed8
