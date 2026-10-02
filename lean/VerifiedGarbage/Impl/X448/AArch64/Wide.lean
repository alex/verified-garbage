import VerifiedGarbage.Impl.X448.AArch64.Common

/-! Eight radix-2⁵⁶ limbs, with two-word product coefficients. All blocks
use caller-saved registers; field operands are staged before output writes. -/
namespace VG.Impl.X448.AArch64.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)

def PACKA : Nat := 3968
def PACKB : Nat := 4032

/-- Accumulate x6 × x9 in the two-word x4:x5 coefficient. -/
def term : List Instr :=
  [.mul .x .x10 .x6 .x9, .umulh .x11 .x6 .x9,
    .adds .x .x4 .x4 .x10, .adcs .x .x5 .x5 .x11]

/-- A diagonal coefficient: input limbs are loaded before each term. -/
def column (a b k : Nat) : List Instr :=
  [.movz .x .x4 0 0, .movz .x .x5 0 0] ++
  (List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 then
    [ld .x6 (a + 8 * i), ld .x9 (b + 8 * (k - i))] ++ term else []) ++
  [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]

/-- Stage sixteen 28-bit limbs as eight 56-bit limbs. -/
def packStep (o a i : Nat) : List Instr :=
  [ld .x4 (a + 16 * i), ld .x5 (a + 16 * i + 8), .lsl .x .x5 .x5 28,
      .add .x .x4 .x4 .x5, st .x4 (o + 8 * i)]

def pack (o a : Nat) : List Instr :=
  (List.range 8).flatMap (packStep o a)

/-- Add a two-word coefficient from ACC to x4:x5. -/
def addCoeff (i : Nat) : List Instr :=
  [ld .x6 (ACC + 16 * i), ld .x9 (ACC + 16 * i + 8),
    .adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9]

def reduceIndices (k : Nat) : List Nat :=
  [k + 8] ++ if k < 4 then [k + 12] else [k + 4, k + 8]

def reduceCol (k : Nat) : List Instr :=
  [ld .x4 (ACC + 16 * k), ld .x5 (ACC + 16 * k + 8)] ++
  (reduceIndices k).flatMap addCoeff ++
  [st .x4 (TMP + 16 * k), st .x5 (TMP + 16 * k + 8)]

def carryRegs : List Instr :=
  [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x11,
    .lsr .x .x6 .x4 56, .lsl .x .x5 .x5 8, .add .x .x6 .x6 .x5,
    .logic .and .x .x4 .x4 .x9]

/-- Carry extraction from a two-word coefficient, with mask x9 and zero x11. -/
def carryStep (o i : Nat) (unpack : Bool) : List Instr :=
  [ld .x4 (TMP + 16 * i), ld .x5 (TMP + 16 * i + 8)] ++ carryRegs ++
  (if unpack then [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12,
    st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)]
   else [st .x4 (o + 16 * i), st .x11 (o + 16 * i + 8)])

def passInit : List Instr :=
  [.movz .x .x6 0 0, .movz .x .x11 0 0,
    .movz .x .x9 0xffff 0, .movk .x .x9 0xffff 1,
    .movk .x .x9 0xffff 2, .movk .x .x9 0x00ff 3]

def pass (o : Nat) (unpack : Bool) : List Instr :=
  passInit ++ (List.range 8).flatMap (fun i => carryStep o i unpack)

/-- Fold the carry into radix-2⁵⁶ limbs 0 and 4. -/
def fold : List Instr :=
  [0, 4].flatMap fun i =>
    [ld .x4 (TMP + 16 * i), .add .x .x4 .x4 .x6, st .x4 (TMP + 16 * i)]

def normalize (o : Nat) : List Instr :=
  pass TMP false ++ fold ++ pass TMP false ++ fold ++ pass o true

/-- Adapter retaining the existing sixteen-limb field-slot interface. -/
def mul (o a b : Nat) : Prog isa := .block (
  pack PACKA a ++ pack PACKB b ++ (List.range 16).flatMap (column PACKA PACKB) ++
  (List.range 8).flatMap reduceCol ++ normalize o)

end VG.Impl.X448.AArch64.Wide
