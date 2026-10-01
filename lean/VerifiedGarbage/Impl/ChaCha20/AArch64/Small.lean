import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4

/-! Vector tails write only the two or three whole blocks available. -/
namespace VG.Impl.ChaCha20.AArch64.Small
open VG VG.AArch64

def lanes (n : Nat) : List (Fin 4) := (List.finRange 4).filter (fun j => j.val < n)

def finish (n : Nat) : List Instr :=
  (List.finRange 16).flatMap Neon4.addWord ++
    (List.finRange 4).flatMap (Neon4.finishRowFor (lanes n))

def chunk (n : Nat) : Prog isa :=
  .seq (.block Neon4.setup) (.seq Neon4.roundLoop (.block (finish n)))

def next (n : Nat) : List Instr :=
  [.ldr .w .x4 .x0 48, .addImm .w .x4 .x4 n, .str .w .x4 .x0 48,
   .addImm .x .x1 .x1 (64*n), .subImm .x .x2 .x2 (64*n)]

def step (n : Nat) : Prog isa := .seq (chunk n) (.block (next n))

def short : Prog isa :=
  .seq (.block [.lsr .x .x5 .x2 7])
  (.ite (.zero .x .x5) Xor.xor
    (.seq (.seq (.block [.lsr .x .x5 .x2 6, .subImm .x .x5 .x5 3, .lsr .x .x5 .x5 63])
      (.ite (.nonzero .x .x5) (step 2) (step 3))) Xor.xor))

def xor : Prog isa :=
  .seq (.block [.lsr .x .x5 .x2 8])
    (.ite (.zero .x .x5) short Neon4.xor)

end VG.Impl.ChaCha20.AArch64.Small
