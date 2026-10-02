/-!
# The AES S-box as a Boolean circuit

The circuit of Boyar and Peralta, "A new combinational logic minimization
technique with applications to cryptology" (SEA 2010,
https://eprint.iacr.org/2009/191.pdf), with 32 AND gates, 83 XOR gates and
4 XNOR gates, as Thomas Pornin's BearSSL transcribes it in
`br_aes_ct64_bitslice_Sbox` (`src/symcipher/aes_ct64.c`, MIT licence).

Applied to 64-bit words bit by bit, it computes 64 S-boxes at once: bit
`j` of every byte of the input is in word `j`. Its inputs are numbered from
the most significant bit: `x₀` is bit 7 and `x₇` bit 0; likewise for the
outputs `s₀ … s₇`. Each target's proof checks the code made from it on
all 256 inputs (e.g. `Proof/Aes/X86/Sbox.lean`); nothing here needs to be
trusted.
-/

namespace VG.Impl.Aes.Circuit

inductive Op
  | xor
  | and
  /-- `a ⊕ ¬b` -/
  | xnor
  deriving DecidableEq, Repr

/-- `dst := a op b`, on variables numbered as below. -/
structure Gate where
  dst : Nat
  op : Op
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

/-! Variables: `x₀ … x₇` are `0 … 7`, `y₁ … y₂₁` are `9 … 29`, `t₀ … t₆₇`
are `30 … 97`, `z₀ … z₁₇` are `98 … 115`, `s₀ … s₇` are `116 … 123`. -/

def x (i : Nat) : Nat := i
def y (i : Nat) : Nat := 8 + i
def t (i : Nat) : Nat := 30 + i
def z (i : Nat) : Nat := 98 + i
def s (i : Nat) : Nat := 116 + i

def xor (d a b : Nat) : Gate := ⟨d, .xor, a, b⟩
def and (d a b : Nat) : Gate := ⟨d, .and, a, b⟩
def xnor (d a b : Nat) : Gate := ⟨d, .xnor, a, b⟩

/-- The top linear transformation. -/
def top : List Gate := [
  xor (y 14) (x 3) (x 5), xor (y 13) (x 0) (x 6), xor (y 9) (x 0) (x 3),
  xor (y 8) (x 0) (x 5), xor (t 0) (x 1) (x 2), xor (y 1) (t 0) (x 7),
  xor (y 4) (y 1) (x 3), xor (y 12) (y 13) (y 14), xor (y 2) (y 1) (x 0),
  xor (y 5) (y 1) (x 6), xor (y 3) (y 5) (y 8), xor (t 1) (x 4) (y 12),
  xor (y 15) (t 1) (x 5), xor (y 20) (t 1) (x 1), xor (y 6) (y 15) (x 7),
  xor (y 10) (y 15) (t 0), xor (y 11) (y 20) (y 9), xor (y 7) (x 7) (y 11),
  xor (y 17) (y 10) (y 11), xor (y 19) (y 10) (y 8), xor (y 16) (t 0) (y 11),
  xor (y 21) (y 13) (y 16), xor (y 18) (x 0) (y 16)]

/-- The non-linear section. -/
def middle : List Gate := [
  and (t 2) (y 12) (y 15), and (t 3) (y 3) (y 6), xor (t 4) (t 3) (t 2),
  and (t 5) (y 4) (x 7), xor (t 6) (t 5) (t 2), and (t 7) (y 13) (y 16),
  and (t 8) (y 5) (y 1), xor (t 9) (t 8) (t 7), and (t 10) (y 2) (y 7),
  xor (t 11) (t 10) (t 7), and (t 12) (y 9) (y 11), and (t 13) (y 14) (y 17),
  xor (t 14) (t 13) (t 12), and (t 15) (y 8) (y 10), xor (t 16) (t 15) (t 12),
  xor (t 17) (t 4) (t 14), xor (t 18) (t 6) (t 16), xor (t 19) (t 9) (t 14),
  xor (t 20) (t 11) (t 16), xor (t 21) (t 17) (y 20), xor (t 22) (t 18) (y 19),
  xor (t 23) (t 19) (y 21), xor (t 24) (t 20) (y 18),
  xor (t 25) (t 21) (t 22), and (t 26) (t 21) (t 23), xor (t 27) (t 24) (t 26),
  and (t 28) (t 25) (t 27), xor (t 29) (t 28) (t 22), xor (t 30) (t 23) (t 24),
  xor (t 31) (t 22) (t 26), and (t 32) (t 31) (t 30), xor (t 33) (t 32) (t 24),
  xor (t 34) (t 23) (t 33), xor (t 35) (t 27) (t 33), and (t 36) (t 24) (t 35),
  xor (t 37) (t 36) (t 34), xor (t 38) (t 27) (t 36), and (t 39) (t 29) (t 38),
  xor (t 40) (t 25) (t 39),
  xor (t 41) (t 40) (t 37), xor (t 42) (t 29) (t 33), xor (t 43) (t 29) (t 40),
  xor (t 44) (t 33) (t 37), xor (t 45) (t 42) (t 41),
  and (z 0) (t 44) (y 15), and (z 1) (t 37) (y 6), and (z 2) (t 33) (x 7),
  and (z 3) (t 43) (y 16), and (z 4) (t 40) (y 1), and (z 5) (t 29) (y 7),
  and (z 6) (t 42) (y 11), and (z 7) (t 45) (y 17), and (z 8) (t 41) (y 10),
  and (z 9) (t 44) (y 12), and (z 10) (t 37) (y 3), and (z 11) (t 33) (y 4),
  and (z 12) (t 43) (y 13), and (z 13) (t 40) (y 5), and (z 14) (t 29) (y 2),
  and (z 15) (t 42) (y 9), and (z 16) (t 45) (y 14), and (z 17) (t 41) (y 8)]

/-- The bottom linear transformation. -/
def bottom : List Gate := [
  xor (t 46) (z 15) (z 16), xor (t 47) (z 10) (z 11), xor (t 48) (z 5) (z 13),
  xor (t 49) (z 9) (z 10), xor (t 50) (z 2) (z 12), xor (t 51) (z 2) (z 5),
  xor (t 52) (z 7) (z 8), xor (t 53) (z 0) (z 3), xor (t 54) (z 6) (z 7),
  xor (t 55) (z 16) (z 17), xor (t 56) (z 12) (t 48), xor (t 57) (t 50) (t 53),
  xor (t 58) (z 4) (t 46), xor (t 59) (z 3) (t 54), xor (t 60) (t 46) (t 57),
  xor (t 61) (z 14) (t 57), xor (t 62) (t 52) (t 58), xor (t 63) (t 49) (t 58),
  xor (t 64) (z 4) (t 59), xor (t 65) (t 61) (t 62), xor (t 66) (z 1) (t 63),
  xor (s 0) (t 59) (t 63), xnor (s 6) (t 56) (t 62), xnor (s 7) (t 48) (t 60),
  xor (t 67) (t 64) (t 65), xor (s 3) (t 53) (t 66), xor (s 4) (t 51) (t 66),
  xor (s 5) (t 47) (t 65), xnor (s 1) (t 64) (s 3), xnor (s 2) (t 55) (t 67)]

def sbox : List Gate := top ++ middle ++ bottom

end VG.Impl.Aes.Circuit
