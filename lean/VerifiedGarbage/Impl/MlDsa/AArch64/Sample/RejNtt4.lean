import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair

/-! Four independent SHAKE128 samplers, computed as two pairs of NEON lanes.
The 1008 bytes per stream and rejection loop match the single-stream sampler. -/
namespace VG.Impl.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

abbrev oBuf : Nat := 840
abbrev oSave : Nat := 7968

def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]

/-- Preserve the scalar registers and the ABI-preserved low vector lanes. -/
def saveG : List Instr :=
  (List.range 10).map (fun i => .str .x (saved[i]!) .x2 (oSave+8*i))

def saveV : List Instr :=
  (List.range 8).flatMap (fun i =>
    [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x2 (oSave+80+8*i)])

def proArgs : List Instr := [mov .x19 .x2,mov .x20 .x0,mov .x21 .x1]

def pro : List Instr := saveG ++ saveV ++ proArgs

def restoreV : List Instr :=
  (List.range 8).flatMap (fun i =>
    [.ldr .x .x8 .x19 (oSave+80+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)])

def restoreG : List Instr :=
  (List.range 9).map (fun i => .ldr .x (saved[i+1]!) .x19 (oSave+8*(i+1)))

def epi : List Instr := [mov .x0 .x27] ++ restoreV ++ restoreG ++ [.ldr .x .x19 .x19 oSave]

def zeroStates : List Instr := [.vop (.movi0 .v0)] ++
  (List.range 50).map fun i => .strq .v0 .x19 (16*i)

/-- Load corresponding full words of the two 34-byte seeds. -/
def seedWord (j : Nat) : List Instr :=
  [.ldr .x .x6 .x3 (8*j),.ldr .x .x7 .x4 (8*j),.vop (.dup .d2 .v0 .x6),
   .vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 (16*j)]

/-- The final two bytes of a seed, without reading past its buffer. -/
def seedLast (r n : Reg) : List Instr :=
  [.ldrb r n 32,.ldrb .x8 n 33,.lsl .x .x8 .x8 8,.add .x r r .x8]

def tailAdd : List Instr :=
  [.movz .x .x9 31 1,.add .x .x6 .x6 .x9,.add .x .x7 .x7 .x9]

def tailStore : List Instr :=
  [.vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x2 64,
   .movz .x .x9 0x8000 3,.vop (.dup .d2 .v0 .x9),.strq .v0 .x2 320]

def tailPack : List Instr := tailAdd ++ tailStore

/-- Complete the padded pair of SHAKE128 states. -/
def seedTail : List Instr := seedLast .x6 .x3 ++ seedLast .x7 .x4 ++ tailPack

def absorbArgs (p : Nat) : List Instr :=
  [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (68*p),.addImm .x .x4 .x3 34]

def absorbBody : List Instr := (List.range 4).flatMap seedWord ++ seedTail

def absorbPair (p : Nat) : List Instr := absorbArgs p ++ absorbBody

def setup : List Instr :=
  [mov .x22 .x19,.addImm .x .x23 .x19 400,.addImm .x .x24 .x19 oBuf,
   .addImm .x .x25 .x19 (oBuf+1008),.addImm .x .x26 .x19 (oBuf+2016),
   .addImm .x .x27 .x19 (oBuf+3024),.movz .x .x28 6 0]

def advance : List Instr :=
  [.addImm .x .x24 .x24 168,.addImm .x .x25 .x25 168,.addImm .x .x26 .x26 168,
   .addImm .x .x27 .x27 168,.subImm .x .x28 .x28 1]

def squeezeStepWith (sha3 : Bool) : Prog isa :=
  .seq (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 .x22 .x24 .x25)
    (.seq (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 .x23 .x26 .x27) (.block advance))

def squeezeStep : Prog isa := squeezeStepWith false

/-- Reuse the verified single-stream rejection loop on stream k's output. -/
def sample (k : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)])
    (.seq zeroPoly (.seq rnLoop (.block (retZ ++ [.logic .and .x .x27 .x27 .x0]))))

def init : List Instr := pro ++ zeroStates ++ absorbPair 0 ++ absorbPair 1

def rejNTT4With (sha3 : Bool) : Prog isa :=
  .seq (.block (init ++ setup))
    (.seq (.loop (squeezeStepWith sha3) (.nonzero .x .x28))
      (.seq (.block [.movz .x .x27 1 0])
        (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi)))))))
def rejNTT4 : Prog isa := rejNTT4With false
end VG.Impl.MlDsa.AArch64.Sample.Rej4
