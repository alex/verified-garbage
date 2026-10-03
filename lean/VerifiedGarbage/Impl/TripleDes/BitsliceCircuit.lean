/-!
# DES S-boxes as AND/OR/XOR/AND-NOT/NOT circuits, for bitslicing

Untrusted. Roman Rusakov's Boolean expressions for the DES S-boxes, as
Openwall's John the Ripper publishes them (`src/nonstd.c`, compiled with
`andn = 0`, `triop = 0`, `regs = 16`, `latency = 2`: the variants John the
Ripper uses for two-operand x86-64; https://www.openwall.com/john/). Gate
counts 49, 44, 46, 33, 48, 46, 46 and 41. Their notice: "Being mathematical
formulas, they are not copyrighted and are free for reuse by anyone."

Applied to words bit by bit, a circuit computes the S-box at every bit
position at once. Variables `0 … 5` are the S-box's input bits, least
significant first (FIPS 46-3's first input bit is variable 5), each gate
defines the next variable, and `outputsᵢ` lists the variables of the output
bits, least significant first. Each target's proof checks the code made from
a circuit on all 64 inputs against `Spec.TripleDes.sBox`; nothing here
needs to be trusted.
-/

namespace VG.Impl.TripleDes.Bitslice

inductive Op
  | and
  | or
  | xor
  /-- `a ∧ ¬b` -/
  | andn
  /-- `¬a` (`b` is ignored) -/
  | not
  deriving DecidableEq, Repr

/-- `dst := a op b`. -/
structure Gate where
  dst : Nat
  op : Op
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def and (d a b : Nat) : Gate := ⟨d, .and, a, b⟩
def or (d a b : Nat) : Gate := ⟨d, .or, a, b⟩
def xor (d a b : Nat) : Gate := ⟨d, .xor, a, b⟩
def andn (d a b : Nat) : Gate := ⟨d, .andn, a, b⟩
def not (d a : Nat) : Gate := ⟨d, .not, a, a⟩

def box0 : List Gate := [
  andn 6 5 1, xor 7 2 6, or 8 3 0, xor 9 5 3,
  and 10 8 9, xor 11 2 10, andn 12 11 7, xor 13 1 0,
  xor 14 3 13, andn 15 7 14, or 16 0 10, xor 17 15 16,
  andn 18 17 12, or 19 5 0, or 20 17 19, andn 21 1 11,
  xor 22 20 21, andn 23 2 19, xor 24 21 23, andn 25 13 9,
  or 26 24 25, andn 27 3 6, xor 28 7 20, andn 29 28 27,
  not 30 29, and 31 8 17, xor 32 30 31, andn 33 22 4,
  xor 34 33 32, xor 35 13 29, or 36 21 35, xor 37 8 36,
  xor 38 5 37, xor 39 32 38, or 40 12 4, xor 41 40 39,
  xor 42 8 20, or 43 26 42, xor 44 38 43, or 45 13 39,
  xor 46 44 45, or 47 18 4, xor 48 47 46, or 49 1 7,
  andn 50 49 44, and 51 18 38, xor 52 50 51, or 53 52 4,
  xor 54 53 26]

def outputs0 : List Nat := [54, 34, 48, 41]

def box1 : List Gate := [
  xor 6 4 1, andn 7 5 0, andn 8 1 7, or 9 4 8,
  andn 10 6 0, and 11 5 6, xor 12 1 11, andn 13 12 10,
  and 14 3 0, xor 15 8 10, and 16 9 15, andn 17 16 14,
  and 18 3 16, not 19 5, xor 20 18 19, xor 21 0 6,
  andn 22 21 14, xor 23 20 22, andn 24 2 17, xor 25 24 23,
  andn 26 4 22, xor 27 12 26, andn 28 20 27, xor 29 3 21,
  xor 30 28 29, andn 31 9 2, xor 32 31 30, xor 33 18 26,
  or 34 29 33, xor 35 9 23, or 36 14 35, xor 37 34 36,
  xor 38 16 23, xor 39 30 38, and 40 36 39, and 41 6 34,
  xor 42 40 41, or 43 42 2, xor 44 43 37, andn 45 42 27,
  or 46 21 35, xor 47 45 46, or 48 13 2, xor 49 48 47]

def outputs1 : List Nat := [49, 44, 25, 32]

def box2 : List Gate := [
  andn 6 5 4, xor 7 3 0, or 8 6 7, xor 9 2 0,
  andn 10 9 5, xor 11 8 10, xor 12 4 7, andn 13 12 0,
  xor 14 8 13, andn 15 11 14, and 16 0 11, or 17 2 16,
  and 18 5 17, xor 19 12 18, andn 20 11 1, xor 21 20 19,
  and 22 7 9, xor 23 5 2, xor 24 14 23, or 25 3 24,
  andn 26 25 22, or 27 10 23, andn 28 19 27, and 29 2 0,
  andn 30 29 4, xor 31 28 30, and 32 14 31, or 33 12 29,
  andn 34 33 32, xor 35 5 34, and 36 26 1, xor 37 36 35,
  not 38 11, or 39 4 38, or 40 3 39, xor 41 12 40,
  xor 42 27 41, andn 43 1 15, xor 44 43 42, and 45 2 38,
  xor 46 19 45, or 47 41 46, xor 48 6 35, xor 49 47 48,
  or 50 31 1, xor 51 50 49]

def outputs2 : List Nat := [21, 51, 37, 44]

def box3 : List Gate := [
  xor 6 5 3, xor 7 3 1, or 8 4 2, xor 9 1 8,
  andn 10 7 9, andn 11 7 4, xor 12 2 11, or 13 6 12,
  andn 14 13 10, xor 15 4 14, and 16 12 15, andn 17 7 16,
  xor 18 6 15, andn 19 18 17, xor 20 10 19, xor 21 4 2,
  or 22 1 11, xor 23 18 22, andn 24 23 21, xor 25 14 24,
  andn 26 0 20, xor 27 26 25, not 28 25, andn 29 20 0,
  xor 30 29 28, xor 31 20 28, andn 32 31 21, or 33 16 32,
  xor 34 23 33, or 35 15 0, xor 36 35 34, and 37 0 15,
  xor 38 37 34]

def outputs3 : List Nat := [38, 36, 30, 27]

def box4 : List Gate := [
  or 6 5 3, andn 7 6 0, xor 8 5 7, xor 9 3 8,
  or 10 2 9, andn 11 7 2, xor 12 3 11, and 13 1 12,
  or 14 5 9, xor 15 13 14, xor 16 2 15, xor 17 0 16,
  or 18 8 17, and 19 1 18, xor 20 8 19, and 21 2 14,
  xor 22 20 21, andn 23 18 5, xor 24 12 23, xor 25 1 10,
  andn 26 25 24, not 27 26, andn 28 27 4, xor 29 28 16,
  andn 30 12 19, xor 31 23 25, or 32 22 31, andn 33 32 30,
  andn 34 10 33, and 35 17 33, xor 36 25 35, and 37 12 14,
  or 38 36 37, xor 39 19 38, and 40 39 4, xor 41 40 22,
  xor 42 5 6, xor 43 33 42, and 44 2 36, xor 45 43 44,
  or 46 34 4, xor 47 46 45, xor 48 10 12, andn 49 48 45,
  xor 50 8 36, xor 51 49 50, and 52 10 4, xor 53 52 51]

def outputs4 : List Nat := [41, 29, 53, 47]

def box5 : List Gate := [
  xor 6 4 1, or 7 4 0, and 8 5 7, xor 9 6 8,
  xor 10 0 9, andn 11 1 10, and 12 5 10, xor 13 4 12,
  xor 14 5 3, or 15 13 14, xor 16 9 15, and 17 3 16,
  andn 18 17 0, or 19 11 13, xor 20 18 19, and 21 20 2,
  xor 22 21 16, xor 23 4 15, andn 24 0 23, xor 25 3 24,
  andn 26 1 17, or 27 25 26, or 28 4 14, xor 29 20 28,
  or 30 8 27, xor 31 29 30, or 32 5 16, and 33 19 32,
  xor 34 25 33, andn 35 34 18, or 36 11 2, xor 37 36 35,
  xor 38 9 34, andn 39 1 38, not 40 28, xor 41 23 40,
  xor 42 39 41, andn 43 42 2, xor 44 43 31, xor 45 0 12,
  xor 46 5 25, and 47 45 46, xor 48 17 41, xor 49 47 48,
  andn 50 27 2, xor 51 50 49]

def outputs5 : List Nat := [22, 37, 44, 51]

def box6 : List Gate := [
  xor 6 2 1, xor 7 3 6, and 8 0 7, and 9 2 6,
  xor 10 4 9, and 11 8 10, and 12 0 9, xor 13 3 12,
  or 14 10 13, xor 15 0 6, xor 16 14 15, andn 17 5 11,
  xor 18 17 16, andn 19 1 7, or 20 10 19, xor 21 8 13,
  xor 22 20 21, xor 23 8 15, andn 24 2 23, andn 25 10 24,
  xor 26 1 21, xor 27 25 26, andn 28 23 12, or 29 24 28,
  xor 30 4 14, and 31 27 30, xor 32 29 31, and 33 32 5,
  xor 34 33 27, andn 35 10 3, or 36 28 35, or 37 9 27,
  and 38 36 37, xor 39 32 38, xor 40 19 29, and 41 0 40,
  or 42 11 41, xor 43 38 42, andn 44 43 5, xor 45 44 22,
  and 46 4 42, not 47 22, xor 48 46 47, xor 49 43 48,
  or 50 39 5, xor 51 50 49]

def outputs6 : List Nat := [18, 34, 51, 45]

def box7 : List Gate := [
  andn 6 3 4, andn 7 1 3, xor 8 2 7, and 9 5 8,
  andn 10 9 6, andn 11 4 8, or 12 5 11, andn 13 4 3,
  xor 14 1 13, and 15 12 14, or 16 9 15, not 17 8,
  xor 18 15 17, andn 19 3 12, xor 20 18 19, xor 21 6 20,
  or 22 10 0, xor 23 22 21, xor 24 5 21, and 25 1 24,
  xor 26 4 20, xor 27 25 26, xor 28 11 27, xor 29 16 27,
  or 30 4 29, xor 31 1 24, xor 32 30 31, and 33 16 0,
  xor 34 33 32, xor 35 14 28, or 36 2 26, xor 37 35 36,
  xor 38 5 37, and 39 38 0, xor 40 39 28, andn 41 35 2,
  and 42 32 41, xor 43 10 37, xor 44 42 43, or 45 44 0,
  xor 46 45 28]

def outputs7 : List Nat := [40, 34, 23, 46]


/-- The circuit of S-box `i` (numbered from 0). -/
def box : Nat → List Gate
  | 0 => box0 | 1 => box1 | 2 => box2 | 3 => box3
  | 4 => box4 | 5 => box5 | 6 => box6 | _ => box7

/-- The variables of S-box `i`'s output bits, least significant first. -/
def outputs : Nat → List Nat
  | 0 => outputs0 | 1 => outputs1 | 2 => outputs2 | 3 => outputs3
  | 4 => outputs4 | 5 => outputs5 | 6 => outputs6 | _ => outputs7

end VG.Impl.TripleDes.Bitslice
