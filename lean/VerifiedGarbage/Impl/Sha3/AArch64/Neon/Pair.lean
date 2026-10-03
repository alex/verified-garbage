import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Vector

namespace VG.Impl.Sha3.AArch64.Neon.Pair
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Two states, with corresponding 64-bit words packed together. -/
def load (p : Reg) : List Instr :=
  (List.range 25).map fun i => .ldrq (vreg i) p (16*i)

def store (p : Reg) : List Instr :=
  (List.range 25).map fun i => .strq (vreg i) p (16*i)

/-- Write one SHAKE128 rate block from each of the paired states. -/
def squeeze (a b : Reg) : List Instr :=
  (List.range 21).flatMap fun i =>
    [.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,
     .str .x .x6 a (8*i),.str .x .x7 b (8*i)]

/-- Keep each round as a short structured block for kernel evaluation. -/
def roundsProg (sha3 : Bool) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (roundsProg sha3 n) (.block (if sha3 then
      Impl.Sha3.AArch64.Sha3.Vector.round n else Vector.round n))

def progWith (sha3 : Bool) (p a b : Reg) : Prog isa :=
  .seq (.block (load p)) (.seq (roundsProg sha3 24) (.seq (.block (store p)) (.block (squeeze a b))))
end VG.Impl.Sha3.AArch64.Neon.Pair
