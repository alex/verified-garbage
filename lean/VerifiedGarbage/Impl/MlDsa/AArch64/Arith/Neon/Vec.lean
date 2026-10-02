import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-! Four canonical ML-DSA coefficients per NEON vector. Widening products
and Montgomery reduction use only the existing AdvSIMD instruction model. -/
namespace VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith (movW)

def consts : List Instr :=
  movW .x9 8380417 ++ movW .x10 4236238847 ++
    [.vop (.dup .s4 .v16 .x9), .vop (.dup .s4 .v17 .x10)]

/-- Reduce lanes below 2q, with q in v16. -/
def csub (d t : VReg) : List Instr :=
  [.vop (.sub .s4 t d .v16), .vop (.umin d d t)]

/-- Four 32x32 products, reduced by Montgomery REDC. The low product
words form m; UMLAL adds m*q before UZP2 extracts the high words. -/
def mont (d z : VReg) : List Instr :=
  [.vop (.umull false .v2 d z), .vop (.umull true .v3 d z),
   .vop (.perm .uzp1 .s4 .v4 .v2 .v3), .vop (.mul .v4 .v4 .v17),
   .vop (.umlal false .v2 .v4 .v16), .vop (.umlal true .v3 .v4 .v16),
   .vop (.perm .uzp2 .s4 d .v2 .v3)]

/-- Forward butterflies: v0 = a+z*b, v5 = a-z*b, both canonical. -/
def bfly : List Instr :=
  mont .v1 .v18 ++ csub .v1 .v4 ++
  [.vop (.mov .v5 .v0), .vop (.add .s4 .v0 .v0 .v1)] ++ csub .v0 .v4 ++
  [.vop (.add .s4 .v5 .v5 .v16), .vop (.sub .s4 .v5 .v5 .v1)] ++ csub .v5 .v4

/-- Inverse butterflies with the negated zeta in Montgomery form. -/
def bflyInv : List Instr :=
  [.vop (.add .s4 .v5 .v0 .v16), .vop (.sub .s4 .v5 .v5 .v1),
   .vop (.add .s4 .v0 .v0 .v1)] ++ csub .v0 .v4 ++
  mont .v5 .v18 ++ csub .v5 .v4
end VG.Impl.MlDsa.AArch64.Arith.Neon
