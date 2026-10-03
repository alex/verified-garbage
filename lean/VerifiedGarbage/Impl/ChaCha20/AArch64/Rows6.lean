import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
import VerifiedGarbage.Impl.ChaCha20.AArch64.Small

/-!
# Six row-oriented ChaCha20 blocks

Each block occupies four vectors, with the four consecutive words of one
row in its lanes. Quarter rounds run on four columns together. EXT aligns
and restores the three nonconstant rows for the diagonal quarter rounds.
The stream wrapper must preserve the low halves of v8–v9 before using this
kernel. v30 is the byte-rotation table and v31 is temporary.
-/
namespace VG.Impl.ChaCha20.AArch64.Rows6
open VG.AArch64

def vreg (k : Fin 24) : VReg :=
  #[.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,
    .v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27,.v28,.v29,.v8,.v9][k]

def row (block : Fin 6) (r : Fin 4) : Fin 24 := ⟨4 * block.val + r.val, by omega⟩

inductive Op
  | add (d a b : Fin 24)
  | xorRol (d a b : Fin 24) (n : Fin 32)
  | permute (d : Fin 24) (n : Fin 4)

def Op.code : Op → List Instr
  | .add d a b => [.vop (.add .s4 (vreg d) (vreg a) (vreg b))]
  | .xorRol d a b n =>
    [.vop (.logic .eor .v31 (vreg a) (vreg b))] ++
    if n.val = 16 then [.vop (.rev .rev32h (vreg d) .v31)]
    else if n.val = 8 then [.vop (.tbl (vreg d) .v31 .v30)]
    else [.vop (.shift .ushr .s4 (vreg d) .v31 (32 - n)),
      .vop (.shift .sli .s4 (vreg d) .v31 n)]
  | .permute d n => [.vop (.ext (vreg d) (vreg d) (vreg d) (4 * n.val))]

def stage (f : Fin 6 → Op) : List Op := (List.finRange 6).map f

def half (r₁ r₂ : Fin 32) : List Op :=
  stage (fun b => .add (row b 0) (row b 0) (row b 1)) ++
  stage (fun b => .xorRol (row b 3) (row b 3) (row b 0) r₁) ++
  stage (fun b => .add (row b 2) (row b 2) (row b 3)) ++
  stage (fun b => .xorRol (row b 1) (row b 1) (row b 2) r₂)

def quarter : List Op := half 16 12 ++ half 8 7

def diagonals (restore : Bool) : List Op :=
  stage (fun b => .permute (row b 1) (if restore then 3 else 1)) ++
  stage (fun b => .permute (row b 2) 2) ++
  stage (fun b => .permute (row b 3) (if restore then 1 else 3))

def roundOps : List Op := quarter ++ diagonals false ++ quarter ++ diagonals true

def doubleRound : List Instr := roundOps.flatMap Op.code

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block doubleRound)

/-- Load one contiguous state row; lane zero of the final row receives
this block's counter offset. -/
def inputRowInto (k : Fin 24) (d : VReg) : List Instr :=
  [.ldrq d .x0 (16 * (k.val % 4))] ++
  if k.val % 4 = 3 then
    [.ldr .w .x4 .x0 48, .addImm .w .x4 .x4 (k.val / 4), .vop (.ins .s4 d 0 .x4)]
  else []

def setupRow (k : Fin 24) : List Instr := inputRowInto k (vreg k)

def setup : List Instr := (List.finRange 24).flatMap setupRow ++ Neon4.setupTable

def addRow (k : Fin 24) : List Instr := inputRowInto k .v31 ++
  [.vop (.add .s4 (vreg k) (vreg k) .v31)]

/-- Load each common row once for its six independent additions. -/
def cachedFeedRow (r : Fin 3) : List Instr :=
  [.ldrq .v31 .x0 (16 * r.val)] ++
    (List.finRange 6).map fun b => Instr.vop (.add .s4
      (vreg (row b ⟨r.val, by omega⟩)) (vreg (row b ⟨r.val, by omega⟩)) .v31)

def feedForward : List Instr :=
  cachedFeedRow 0 ++ cachedFeedRow 1 ++ cachedFeedRow 2 ++
    (List.finRange 6).flatMap (fun b => addRow (row b 3))

/-- Rows already have the output byte order, so no transpose is needed. -/
def xorRow (k : Fin 24) : List Instr :=
  [.ldrq .v31 .x1 (16 * k.val), .vop (.logic .eor .v31 .v31 (vreg k)),
   .strq .v31 .x1 (16 * k.val)]

def finish : List Instr := feedForward ++ (List.finRange 24).flatMap xorRow

/-- Six-block core. The outer wrapper supplies ABI preservation and advances
pointers and the counter after this chunk. -/
def chunk : Prog isa := .seq (.block setup) (.seq (rounds 10) (.block finish))

def check : List Instr :=
  [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 6,.lsr .x .x5 .x5 63]

def next : List Instr :=
  [.ldr .w .x4 .x0 48,.addImm .w .x4 .x4 6,.str .w .x4 .x0 48,
   .addImm .x .x1 .x1 384,.subImm .x .x2 .x2 384] ++ check

def body : Prog isa := .seq chunk (.block next)

/-- Bulk core before the two callee-saved vectors are wrapped. -/
def raw : Prog isa := .seq (.block check)
  (.seq (.ite (.nonzero .x .x5) (.block []) (.loop body (.zero .x .x5)))
    VG.Impl.ChaCha20.AArch64.Small.xor)

def save : List Instr := [.strq .v8 .x3 256,.strq .v9 .x3 272]
def restore : List Instr := [.ldrq .v8 .x3 256,.ldrq .v9 .x3 272]
def bulk : Prog isa := .seq (.block check)
  (.ite (.nonzero .x .x5) (.block []) (.loop body (.zero .x .x5)))

def xor : Prog isa := .seq (.block save)
  (.seq bulk (.seq (.block restore) VG.Impl.ChaCha20.AArch64.Small.xor))

end VG.Impl.ChaCha20.AArch64.Rows6
