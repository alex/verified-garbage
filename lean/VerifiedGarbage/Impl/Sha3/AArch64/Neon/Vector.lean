import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

/-! Portable NEON Keccak-f[1600] on two independent states. Each register
holds the same state word from both streams. Only baseline AdvSIMD is used. -/
namespace VG.Impl.Sha3.AArch64.Neon.Vector
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg constant)

/-- Rotate both 64-bit lanes. `d` and `n` are distinct. -/
def rol (d n : VReg) (k : Nat) : List Instr :=
  [.vop (.shift .ushr .d2 d n (64-k)), .vop (.shift .sli .d2 d n k)]

/-- Compute all column parities before changing any state word. -/
def parity (x : Nat) : List Instr :=
  [.vop (.logic .eor (vreg (25+x)) (vreg x) (vreg (x+5))),
   .vop (.logic .eor (vreg (25+x)) (vreg (25+x)) (vreg (x+10))),
   .vop (.logic .eor (vreg (25+x)) (vreg (25+x)) (vreg (x+15))),
   .vop (.logic .eor (vreg (25+x)) (vreg (25+x)) (vreg (x+20)))]

def correction (x : Nat) : List Instr :=
  rol .v30 (vreg (25+(x+1)%5)) 1 ++
  [.vop (.logic .eor .v30 (vreg (25+(x+4)%5)) .v30)] ++
    (List.range 5).map fun y => .vop (.logic .eor (vreg (x+5*y)) (vreg (x+5*y)) .v30)

def theta : List Instr := (List.range 5).flatMap parity ++ (List.range 5).flatMap correction

/-- The nonzero lane cycle of pi, paired with rho's rotation offsets. -/
def cycle : List (Nat × Nat) :=
  [(10,1),(7,3),(11,6),(17,10),(18,15),(3,21),(5,28),(16,36),
   (8,45),(21,55),(24,2),(4,14),(15,27),(23,41),(19,56),(13,8),
   (12,25),(2,43),(20,62),(14,18),(22,39),(9,61),(6,20),(1,44)]

/-- Keep the displaced word while installing its predecessor. -/
def rhoPiStep (p : Nat × Nat) : List Instr :=
  [.vop (.mov .v26 (vreg p.1))] ++ rol (vreg p.1) .v25 p.2 ++ [.vop (.mov .v25 .v26)]

def rhoPi : List Instr := [.vop (.mov .v25 .v1)] ++ cycle.flatMap rhoPiStep

/-- Preserve a row before computing its nonlinear layer. -/
def saveRow (y : Nat) : List Instr :=
  (List.range 5).map fun x => .vop (.mov (vreg (25+x)) (vreg (x+5*y)))

def chiWord (x y : Nat) : List Instr :=
  [.vop (.logic .bic .v30 (vreg (25+(x+2)%5)) (vreg (25+(x+1)%5))),
   .vop (.logic .eor (vreg (x+5*y)) (vreg (25+x)) .v30)]

def row (y : Nat) : List Instr := saveRow y ++ (List.range 5).flatMap (fun x => chiWord x y)

def chi : List Instr := (List.range 5).flatMap row

def iota : List Instr := [.vop (.dup .d2 .v25 .x16),.vop (.logic .eor .v0 .v0 .v25)]

def round (r : Nat) : List Instr := constant (Spec.Sha3.RC r) ++ theta ++ rhoPi ++ chi ++ iota

def rounds : List Instr := (List.range 24).flatMap round
end VG.Impl.Sha3.AArch64.Neon.Vector
