import VerifiedGarbage.Impl.X448.AArch64.Tail

/-! Shared Curve448 field arithmetic: eight radix-2⁵⁶ limbs with headroom.
Slots retain a 128-byte stride, but only their first eight words are field limbs.
Products stage all coefficients before writes, allowing either output alias.
-/
namespace VG.Impl.Curve448.AArch64
open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)

/-- Collect eight low coefficient words into a persistent field slot. -/
def collect (o : Nat) : List Instr := (List.range 8).flatMap fun i =>
  [ld .x4 (TMP + 16 * i), st .x4 (o + 8 * i)]

def normalize (o : Nat) : List Instr :=
  X448.AArch64.Wide.pass TMP false ++ X448.AArch64.Wide.fold ++
  X448.AArch64.Tail.pass TMP false ++ X448.AArch64.Wide.fold ++ collect o

def product (o a b : Nat) : Prog isa := .block (
  (List.range 16).flatMap (X448.AArch64.Wide.column a b) ++
  (List.range 8).flatMap X448.AArch64.Wide.reduceCol ++ normalize o)

def sqr (o a : Nat) : Prog isa := .block (
  X448.AArch64.Cached.loadCached a ++
  (List.range 16).flatMap X448.AArch64.Symmetric.column ++
  (List.range 8).flatMap X448.AArch64.Wide.reduceCol ++ normalize o)

def mul (o a b : Nat) : Prog isa := if a = b then sqr o a else product o a b

/-- Preserve full coefficients in TMP before reducing them. -/
def addEval (a b i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 .x5,
    .movz .x .x5 0 0]

def subEval (a b i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), .movz .x .x5 (if i = 4 then 0xfff8 else 0xfffc) 0,
    .movk .x .x5 0xffff 1, .movk .x .x5 0xffff 2, .movk .x .x5 0x03ff 3,
    .add .x .x4 .x4 .x5, ld .x5 (b + 8 * i), .sub .x .x4 .x4 .x5,
    .movz .x .x5 0 0]

def storeCoeff (i : Nat) : List Instr := [st .x4 (TMP + 16 * i), st .x5 (TMP + 16 * i + 8)]
def addStep (a b i : Nat) : List Instr := addEval a b i ++ storeCoeff i
def subStep (a b i : Nat) : List Instr := subEval a b i ++ storeCoeff i

/-- One carry pass and fold suffice for pointwise add/sub headroom. -/
def pointFinish (o : Nat) : List Instr :=
  X448.AArch64.Tail.pass TMP false ++ X448.AArch64.Wide.fold ++ collect o

def add (o a b : Nat) : List Instr :=
  (List.range 8).flatMap (addStep a b) ++ pointFinish o

def sub (o a b : Nat) : List Instr :=
  (List.range 8).flatMap (subStep a b) ++ pointFinish o

def smallEval (a i : Nat) : List Instr :=
  [ld .x6 (a + 8 * i), .movz .x .x5 39081 0,
    .mul .x .x4 .x6 .x5, .umulh .x5 .x6 .x5]
def smallStep (a i : Nat) : List Instr := smallEval a i ++ storeCoeff i

def small (o a : Nat) : List Instr :=
  (List.range 8).flatMap (smallStep a) ++ normalize o

def copy (o a : Nat) : List Instr := (List.range 8).flatMap fun i =>
  [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]

def cswap (x y : Nat) : List Instr := (List.range 8).flatMap fun i =>
  [ld .x4 (x + 8 * i), ld .x5 (y + 8 * i), .logic .eor .x .x7 .x4 .x5,
    .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
    .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * i), st .x5 (y + 8 * i)]

/-- Decode the legacy input slots once, outside the ladder. -/
def fromLegacy (o : Nat) : List Instr :=
  X448.AArch64.Wide.pack X448.AArch64.Wide.PACKA o ++ copy o X448.AArch64.Wide.PACKA

/-- Stage a weak element for canonical normalization at the output boundary. -/
def legacyEval (o i : Nat) : List Instr := [ld .x4 (o + 8 * i), .movz .x .x5 0 0]
def toLegacy (o : Nat) : List Instr :=
  (List.range 8).flatMap (fun i => legacyEval o i ++ storeCoeff i) ++
  X448.AArch64.Tail.normalize o
end VG.Impl.Curve448.AArch64
