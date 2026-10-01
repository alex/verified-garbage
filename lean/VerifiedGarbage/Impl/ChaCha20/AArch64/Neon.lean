import VerifiedGarbage.TCB.AArch64.Isa

/-!
# ChaCha20 with four NEON lanes

The four rows of one ChaCha state occupy v0–v3. Each vector quarter round
computes four independent scalar quarter rounds. EXT changes the row
alignment for the diagonal round and restores it afterwards. v4 is the
only temporary. All registers are caller-saved; no stack or extra CPU
extension is needed beyond the target's baseline AdvSIMD support.
-/

namespace VG.Impl.ChaCha20.AArch64.Neon

open VG.AArch64

def rowReg (i : Nat) : VReg := [.v0, .v1, .v2, .v3].getD i .v0

/-- XOR followed by a per-word rotation, using v4 as the source of both shifts. -/
def xorRot (d n m : VReg) (k : Nat) : List Instr :=
  [.vop (.logic .eor .v4 n m), .vop (.shift .ushr .s4 d .v4 (32 - k)),
   .vop (.shift .sli .s4 d .v4 k)]

def qr : List Instr :=
  [.vop (.add .s4 .v0 .v0 .v1)] ++ xorRot .v3 .v3 .v0 16 ++
  [.vop (.add .s4 .v2 .v2 .v3)] ++ xorRot .v1 .v1 .v2 12 ++
  [.vop (.add .s4 .v0 .v0 .v1)] ++ xorRot .v3 .v3 .v0 8 ++
  [.vop (.add .s4 .v2 .v2 .v3)] ++ xorRot .v1 .v1 .v2 7

def diagonal : List Instr :=
  [.vop (.ext .v1 .v1 .v1 4), .vop (.ext .v2 .v2 .v2 8), .vop (.ext .v3 .v3 .v3 12)]

def undiagonal : List Instr :=
  [.vop (.ext .v1 .v1 .v1 12), .vop (.ext .v2 .v2 .v2 8), .vop (.ext .v3 .v3 .v3 4)]

def doubleRound : Prog isa :=
  .seq (.block qr) (.seq (.block diagonal) (.seq (.block qr) (.block undiagonal)))

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

def load : List Instr := (List.range 4).map fun i => .ldrq (rowReg i) .x0 (16 * i)

def finishRow (i : Nat) : List Instr :=
  [.ldrq .v4 .x0 (16 * i), .vop (.add .s4 (rowReg i) (rowReg i) .v4),
   .strq (rowReg i) .x1 (16 * i)]

def finish : List Instr := (List.range 4).flatMap finishRow

def block : Prog isa := .seq (.block load) (.seq (rounds 10) (.block finish))

end VG.Impl.ChaCha20.AArch64.Neon
