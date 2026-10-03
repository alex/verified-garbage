import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Spec.MlDsa

/-! Four butterflies per vector. The last two layers gather two or four
blocks into the same lane layout, without using callee-saved vector registers. -/
namespace VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Arith (storeTab movW)

def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m * 2^32 % 8380417

def negZetaTab (m : Nat) : Nat :=
  ((8380417 - 1753 ^ Spec.MlDsa.bitRev8 m % 8380417) % 8380417) * 2^32 % 8380417

def stepZ (up : Bool) : Instr :=
  if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4

/-- Arrange two or four block zetas in butterfly lane order. -/
def zetaPerms (len : Nat) (up : Bool) : List Instr :=
  (if len = 2 then [.vop (.perm .zip1 .s4 .v18 .v18 .v18)] else []) ++
    if up then [] else
      (if len = 1 then [.vop (.rev .rev64s .v18 .v18)] else []) ++ [.vop (.ext .v18 .v18 .v18 8)]

def packedZetas (len : Nat) (up : Bool) : List Instr :=
  (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))]) ++
  [.ldrq .v18 .x3 0] ++ zetaPerms len up ++
  [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]

/-- Load one zeta per block, replicated across its lanes. -/
def zetas (len : Nat) (up : Bool) : List Instr :=
  if len = 2 then packedZetas len up
  else if len = 1 then packedZetas len up
  else [.ldr .w .x6 .x3 0, stepZ up, .vop (.dup .s4 .v18 .x6)]

def body (bf : List Instr) (len : Nat) : List Instr :=
  [.ldrq .v0 .x2 0, .ldrq .v1 .x2 (4*len)] ++ bf ++
  [.strq .v0 .x2 0, .strq .v5 .x2 (4*len), .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def block (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block (zetas len up ++ [.movz .x .x5 (BitVec.ofNat 16 (len/4)) 0]))
    (.seq (.loop (.block (body bf len)) (.nonzero .x .x5))
      (.block [.addImm .x .x2 .x2 (4*len), .subImm .x .x4 .x4 1]))

def gather (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v0 .v6 .v7), .vop (.perm .trn2 .d2 .v1 .v6 .v7)]
  else [.vop (.perm .uzp1 .s4 .v0 .v6 .v7), .vop (.perm .uzp2 .s4 .v1 .v6 .v7)]

def scatter (len : Nat) : List Instr :=
  if len = 2 then
    [.vop (.perm .trn1 .d2 .v6 .v0 .v5), .vop (.perm .trn2 .d2 .v7 .v0 .v5)]
  else [.vop (.perm .zip1 .s4 .v6 .v0 .v5), .vop (.perm .zip2 .s4 .v7 .v0 .v5)]

def packedBody (bf : List Instr) (len : Nat) (up : Bool) : List Instr :=
  [.ldrq .v6 .x2 0, .ldrq .v7 .x2 16] ++ zetas len up ++ gather len ++ bf ++ scatter len ++
  [.strq .v6 .x2 0, .strq .v7 .x2 16, .addImm .x .x2 .x2 32, .subImm .x .x5 .x5 1]

/-- The zeta range of a layer is known statically. -/
def layer (bf : List Instr) (len : Nat) (up : Bool) : Prog isa :=
  .seq (.block [mov .x2 .x0, .addImm .x .x3 .x1 (4*(if up then 128/len else 256/len-1))])
    (if len < 4 then
      .seq (.block [.movz .x .x5 32 0])
        (.loop (.block (packedBody bf len up)) (.nonzero .x .x5))
     else .seq (.block [.movz .x .x4 (BitVec.ofNat 16 (128/len)) 0])
       (.loop (block bf len up) (.nonzero .x .x4)))

def layers (bf : List Instr) (up : Bool) : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (layer bf len up) (layers bf up lens)

def pro (tab : Nat → Nat) : List Instr := storeTab tab 256 .x1 ++ consts

def ntt : Prog isa := .seq (.block (pro zetaTab)) (layers bfly true [128,64,32,16,8,4,2,1])

def scaleBody : List Instr :=
  [.ldrq .v0 .x2 0] ++ mont .v0 .v18 ++ csub .v0 .v4 ++
    [.strq .v0 .x2 0, .addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1]

def scale : Prog isa :=
  .seq (.block (movW .x6 16382 ++
    [.vop (.dup .s4 .v18 .x6), mov .x2 .x0, .movz .x .x5 64 0]))
    (.loop (.block scaleBody) (.nonzero .x .x5))

def nttInv : Prog isa := .seq (.block (pro negZetaTab))
  (.seq (layers bflyInv false [1,2,4,8,16,32,64,128]) scale)
end VG.Impl.MlDsa.AArch64.Arith.Neon
