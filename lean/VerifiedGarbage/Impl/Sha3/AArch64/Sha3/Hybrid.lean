import VerifiedGarbage.Impl.Sha3.AArch64

/-! Each state lane has its own register: twenty vectors and five GPRs.
Four vector temporaries suffice because pi maps the five GPR lanes to a
line: each chi row contains either one GPR or five GPRs. -/

namespace VG.Impl.Sha3.AArch64.Sha3.Hybrid

open VG.AArch64
open VG.Impl.Sha3 (piSrc rhoOff)
/-- Pi changes the compile-time lane allocation; after 24 rounds it is the identity. -/
def loc : Nat → Nat → Nat
  | 0, i => i
  | r + 1, i => loc r (piSrc (i % 5) (i / 5))

inductive Slot
  | v (r : VReg)
  | g (r : Reg)
  deriving DecidableEq, Repr

def vreg (i : Nat) : VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17,
   .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27].getD i .v0

def greg (i : Nat) : Reg := [.x4, .x5, .x6, .x7, .x8].getD i .x4

def creg (x : Nat) : Reg := [.x9, .x10, .x11, .x12, .x13].getD x .x9

def laneSlot (i : Nat) : Slot := if i < 20 then .v (vreg i) else .g (greg (i - 20))

def readSlot (d : VReg) : Slot → List Instr
  | .v n => [.vop (.mov d n)]
  | .g n => [.vop (.dup .d2 d n)]

def writeSlot (n : VReg) : Slot → List Instr
  | .v d => [.vop (.mov d n)]
  | .g d => [.umov .x d n 0]

def columnSlow (r x : Nat) : List Instr :=
  readSlot .v28 (laneSlot (loc r x)) ++ readSlot .v29 (laneSlot (loc r (x + 5))) ++
  readSlot .v30 (laneSlot (loc r (x + 10))) ++ [.vop (.eor3 .v28 .v28 .v29 .v30)] ++
  readSlot .v29 (laneSlot (loc r (x + 15))) ++ readSlot .v30 (laneSlot (loc r (x + 20))) ++
  [.vop (.eor3 .v28 .v28 .v29 .v30), .umov .x (creg x) .v28 0]

def mixedColumn (a b c d : VReg) (g dst : Reg) : List Instr :=
  [.vop (.eor3 .v28 a b c), .vop (.logic .eor .v28 .v28 d),
   .umov .x dst .v28 0, .logic .eor .x dst dst g]

def vectorColumn (a b c d e : VReg) (dst : Reg) : List Instr :=
  [.vop (.eor3 .v28 a b c), .vop (.eor3 .v28 .v28 d e), .umov .x dst .v28 0]

def integerColumn (a b c d e dst : Reg) : List Instr :=
  [.logic .eor .x dst a b, .logic .eor .x dst dst c,
   .logic .eor .x dst dst d, .logic .eor .x dst dst e]

def column (r x : Nat) : List Instr :=
  match laneSlot (loc r x), laneSlot (loc r (x + 5)), laneSlot (loc r (x + 10)),
      laneSlot (loc r (x + 15)), laneSlot (loc r (x + 20)) with
  | .v a, .v b, .v c, .v d, .v e => vectorColumn a b c d e (creg x)
  | .g a, .g b, .g c, .g d, .g e => integerColumn a b c d e (creg x)
  | .g g, .v a, .v b, .v c, .v d => mixedColumn a b c d g (creg x)
  | .v a, .g g, .v b, .v c, .v d => mixedColumn a b c d g (creg x)
  | .v a, .v b, .g g, .v c, .v d => mixedColumn a b c d g (creg x)
  | .v a, .v b, .v c, .g g, .v d => mixedColumn a b c d g (creg x)
  | .v a, .v b, .v c, .v d, .g g => mixedColumn a b c d g (creg x)
  | _, _, _, _, _ => columnSlow r x

/-- Apply theta and rho in place, then interpret the resulting allocation as pi. -/
def rotateSlot (a : Slot) (sh : Nat) : List Instr :=
  match a with
  | .v v => [.vop (.xar v v .v28 sh)]
  | .g g => [.logic .eor .x g g .x17, .ror .x g g sh]

def rotateLane (r x y : Nat) : List Instr :=
  rotateSlot (laneSlot (loc r (x + 5 * y))) ((64 - rhoOff (x + 5 * y)) % 64)

def rotateColumn (r x : Nat) : List Instr :=
  [.ror .x .x17 (creg ((x + 1) % 5)) 63,
   .logic .eor .x .x17 .x17 (creg ((x + 4) % 5)), .vop (.dup .d2 .v28 .x17)] ++ (List.range 5).flatMap (rotateLane r x)

def savedSlot (s : Slot) (i : Nat) : Slot := match s with
  | .v _ => .v (if i = 0 then .v28 else .v29)
  | .g _ => .g (if i = 0 then .x14 else .x15)

def saveSlot (s : Slot) (i : Nat) : List Instr := match s with
  | .v v => [.vop (.mov (if i = 0 then .v28 else .v29) v)]
  | .g g => [VG.Impl.Sha3.AArch64.mov (if i = 0 then .x14 else .x15) g]

def rowSlot (r x y : Nat) : Slot := laneSlot (loc (r + 1) (x + 5 * y))

def isGpr : Slot → Bool | .g _ => true | .v _ => false

/-- A row with one GPR input needs only one transfer, before any chi output. -/
def cacheSource (r y : Nat) : Option Reg :=
  match rowSlot r 0 y, rowSlot r 1 y, rowSlot r 2 y, rowSlot r 3 y, rowSlot r 4 y with
  | .g g, .v _, .v _, .v _, .v _ => some g
  | .v _, .g g, .v _, .v _, .v _ => some g
  | .v _, .v _, .g g, .v _, .v _ => some g
  | .v _, .v _, .v _, .g g, .v _ => some g
  | .v _, .v _, .v _, .v _, .g g => some g
  | _, _, _, _, _ => none

def cacheRow (r y : Nat) : List Instr := match cacheSource r y with
  | some g => [.vop (.dup .d2 .v30 g)]
  | none => []

def chiBaseSlot (r x y : Nat) : Slot :=
  let s := rowSlot r x y
  if x < 2 then savedSlot s x else s

def chiSlot (r x y : Nat) : Slot :=
  let s := chiBaseSlot r x y
  if cacheSource r y ≠ none ∧ isGpr s = true then .v .v30 else s

def chiTemp (allGpr : Bool) (i : Nat) : VReg :=
  if allGpr then [.v28, .v29, .v30].getD i .v30 else .v30

def operand (s : Slot) (t : VReg) : VReg := match s with | .v v => v | .g _ => t

def prepare (s : Slot) (t : VReg) : List Instr := match s with
  | .v _ => []
  | .g g => [.vop (.dup .d2 t g)]

def chiCore (a b c : Slot) (ta tb tc dest : VReg) (iota : Bool) : List Instr :=
  prepare a ta ++ prepare b tb ++ prepare c tc ++
  [.vop (.bcax dest (operand a ta) (operand c tc) (operand b tb))] ++
  (if iota then [.vop (.dup .d2 .v31 .x16), .vop (.logic .eor dest dest .v31)] else [])

def chiVector (r x y : Nat) : List Instr :=
  let a := chiSlot r x y
  let b := chiSlot r ((x + 1) % 5) y
  let c := chiSlot r ((x + 2) % 5) y
  let allGpr := isGpr a && isGpr b && isGpr c
  let ta := chiTemp allGpr 0
  let tb := chiTemp allGpr 1
  let tc := chiTemp allGpr 2
  let dest := match rowSlot r x y with | .v v => v | .g _ => .v31
  chiCore a b c ta tb tc dest (decide (x = 0 ∧ y = 0)) ++
  (match rowSlot r x y with | .v _ => [] | .g g => [.umov .x g .v31 0])

def chiInteger (a b c dest : Reg) (iota : Bool) : List Instr :=
  [.logic .and .x .x17 b c, .logic .eor .x .x17 .x17 c,
   .logic .eor .x dest .x17 a] ++
  (if iota then [.logic .eor .x dest dest .x16] else [])

def chi (r x y : Nat) : List Instr :=
  match chiSlot r x y, chiSlot r ((x + 1) % 5) y, chiSlot r ((x + 2) % 5) y,
      rowSlot r x y with
  | .g a, .g b, .g c, .g dest => chiInteger a b c dest (decide (x = 0 ∧ y = 0))
  | _, _, _, _ => chiVector r x y

def row (r y : Nat) : List Instr :=
  (saveSlot (rowSlot r 0 y) 0 ++ saveSlot (rowSlot r 1 y) 1 ++ cacheRow r y) ++ (List.range 5).flatMap (fun x => chi r x y)

def roundConstant (r : Nat) : List Instr :=
  let rc := VG.Spec.Sha3.RC r
  [.movz .x .x16 (rc.extractLsb' 0 16) 0, .movk .x .x16 (rc.extractLsb' 16 16) 1,
   .movk .x .x16 (rc.extractLsb' 32 16) 2, .movk .x .x16 (rc.extractLsb' 48 16) 3]

def round (r : Nat) : List Instr :=
  roundConstant r ++ (List.range 5).flatMap (column r) ++
    (List.range 5).flatMap (rotateColumn r) ++ (List.range 5).flatMap (row r)

def loadLane (i : Nat) : List Instr := match laneSlot i with
  | .v v => [.ldr .x .x17 .x0 (8 * i), .vop (.dup .d2 v .x17)]
  | .g g => [.ldr .x g .x0 (8 * i)]

def storeLane (i : Nat) : List Instr := match laneSlot i with
  | .v v => [.umov .x .x17 v 0, .str .x .x17 .x0 (8 * i)]
  | .g g => [.str .x g .x0 (8 * i)]

def load : List Instr := (List.range 25).flatMap loadLane

def store : List Instr := (List.range 25).flatMap storeLane

def permute : Prog isa := .block (load ++ (List.range 24).flatMap round ++ store)

end VG.Impl.Sha3.AArch64.Sha3.Hybrid
