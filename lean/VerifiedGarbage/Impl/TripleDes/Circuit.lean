import VerifiedGarbage.Impl.Aes.Circuit

/-!
# DES Boolean S-box circuits

Untrusted. These circuits are synthesized from the specification's S-boxes
using Davio decomposition and shared subexpressions. Inputs 0–5 and outputs
0–3 are numbered least significant bit first. The proof checks all 64
inputs against FIPS 46-3, and checks the allocated machine code independently.
The existing AES circuit gate representation and allocator are reused;
no cryptographic AES operation is called.
-/

namespace VG.Impl.TripleDes.Circuit

open VG.Impl.Aes.Circuit

def box0 : List Gate := [
  xor 6 0 0, xnor 8 0 6, and 9 4 8,
  xor 10 0 4, and 11 1 10, xor 12 9 11,
  xor 13 8 9, and 14 1 13, xor 15 0 14,
  and 16 5 15, xor 17 12 16, and 18 4 0,
  xnor 19 18 6, and 20 1 19, xor 21 18 20,
  xnor 22 4 6, xor 23 22 20, and 24 5 23,
  xor 25 21 24, and 26 3 25, xor 27 17 26,
  and 28 1 4, xor 29 19 28, and 30 1 22,
  xor 31 8 30, and 32 5 31, xor 33 29 32,
  and 34 1 8, xor 35 13 34, and 36 5 35,
  and 37 3 36, xor 38 33 37, and 39 2 38,
  xor 40 27 39, xor 41 8 18, xor 42 41 30,
  xnor 43 9 6, and 44 1 41, xor 45 43 44,
  and 46 5 45, xor 47 42 46, xnor 48 13 6,
  xor 49 48 30, and 50 1 9, xor 51 9 50,
  and 52 5 51, xor 53 49 52, and 54 3 53,
  xor 55 47 54, xor 56 45 52, and 57 1 0,
  xor 58 43 57, and 59 5 58, xor 60 13 59,
  and 61 3 60, xor 62 56 61, and 63 2 62,
  xor 64 55 63, xor 65 13 57, and 66 5 49,
  xor 67 65 66, xor 68 19 34, and 69 1 48,
  xor 70 43 69, and 71 5 70, xor 72 68 71,
  and 73 3 72, xor 74 67 73, and 75 5 20,
  xor 76 49 75, xor 77 0 57, xor 78 77 59,
  and 79 3 78, xor 80 76 79, and 81 2 80,
  xor 82 74 81, xnor 83 10 6, xor 84 83 1,
  xnor 85 20 6, and 86 5 85, xor 87 84 86,
  xnor 88 23 6, and 89 5 88, xor 90 22 89,
  and 91 3 90, xor 92 87 91, xor 93 13 28,
  and 94 5 93, xor 95 57 94, xor 96 13 1,
  and 97 5 96, xor 98 84 97, and 99 3 98,
  xor 100 95 99, and 101 2 100, xor 102 92 101]

def outputs0 : List Nat := [40, 64, 82, 102]

def box1 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 5 6,
  and 9 1 5, xor 10 5 9, and 11 0 10,
  xor 12 8 11, xnor 13 9 6, and 14 0 13,
  xor 15 10 14, and 16 4 15, xor 17 12 16,
  and 18 1 8, xor 19 8 18, xnor 20 10 6,
  and 21 0 20, xor 22 19 21, xnor 23 19 6,
  and 24 0 23, xor 25 1 24, and 26 4 25,
  xor 27 22 26, and 28 3 27, xor 29 17 28,
  and 30 0 18, xor 31 7 30, xor 32 5 1,
  and 33 0 32, xor 34 1 33, and 35 4 34,
  xor 36 31 35, and 37 2 36, xor 38 29 37,
  xnor 39 32 6, and 40 0 9, xor 41 39 40,
  xor 42 20 33, and 43 4 42, xor 44 41 43,
  xor 45 23 16, and 46 3 45, xor 47 44 46,
  and 48 0 19, xor 49 5 48, and 50 4 49,
  xor 51 13 50, and 52 0 8, xor 53 19 52,
  and 54 4 5, xor 55 53 54, and 56 3 55,
  xor 57 51 56, and 58 2 57, xor 59 47 58,
  xor 60 39 0, xor 61 60 4, xor 62 13 40,
  and 63 4 62, xor 64 0 63, and 65 3 64,
  xor 66 61 65, and 67 0 1, xor 68 7 67,
  xor 69 13 14, and 70 4 69, xor 71 68 70,
  and 72 3 67, xor 73 71 72, and 74 2 73,
  xor 75 66 74, xor 76 39 14, and 77 4 21,
  xor 78 76 77, xnor 79 40 6, xor 80 8 52,
  and 81 4 80, xor 82 79 81, and 83 3 82,
  xor 84 78 83, xor 85 18 40, xnor 86 85 6,
  and 87 4 86, xor 88 85 87, and 89 2 88,
  xor 90 84 89]

def outputs1 : List Nat := [38, 59, 75, 90]

def box2 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 5 6,
  and 9 4 8, xor 10 5 9, and 11 4 5,
  xor 12 8 11, and 13 0 12, xor 14 10 13,
  xnor 15 12 6, and 16 0 11, xor 17 15 16,
  and 18 1 17, xor 19 14 18, and 20 1 12,
  xor 21 17 20, and 22 3 21, xor 23 19 22,
  and 24 0 5, xor 25 7 24, and 26 1 8,
  xor 27 25 26, and 28 3 16, xor 29 27 28,
  and 30 2 29, xor 31 23 30, xor 32 8 4,
  xor 33 32 13, xnor 34 9 6, and 35 0 9,
  xor 36 34 35, and 37 1 36, xor 38 33 37,
  xnor 39 4 6, and 40 0 39, xor 41 4 40,
  and 42 0 8, xor 43 8 42, and 44 1 43,
  xor 45 41 44, and 46 3 45, xor 47 38 46,
  xnor 48 14 6, xnor 49 33 6, and 50 1 49,
  xor 51 48 50, xnor 52 10 6, and 53 0 52,
  xor 54 34 53, xnor 55 42 6, and 56 1 55,
  xor 57 54 56, and 58 3 57, xor 59 51 58,
  and 60 2 59, xor 61 47 60, and 62 0 34,
  xor 63 15 62, xnor 64 36 6, and 65 1 64,
  xor 66 63 65, xor 67 36 37, and 68 3 67,
  xor 69 66 68, xor 70 9 40, xor 71 70 56,
  and 72 1 24, xor 73 9 72, and 74 3 73,
  xor 75 71 74, and 76 2 75, xor 77 69 76,
  xor 78 34 24, xor 79 78 1, xnor 80 32 6,
  and 81 0 80, xor 82 39 81, and 83 1 82,
  xor 84 12 83, and 85 3 84, xor 86 79 85,
  xor 87 10 42, xor 88 52 53, and 89 1 88,
  xor 90 87 89, and 91 1 42, xor 92 52 91,
  and 93 3 92, xor 94 90 93, and 95 2 94,
  xor 96 86 95]

def outputs2 : List Nat := [31, 61, 77, 96]

def box3 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 3 6,
  and 9 1 3, xor 10 8 9, and 11 5 10,
  xor 12 8 11, xor 13 3 1, xnor 14 13 6,
  and 15 5 14, xor 16 13 15, and 17 4 16,
  xor 18 12 17, xnor 19 1 6, xor 20 1 15,
  and 21 4 20, xor 22 19 21, and 23 2 22,
  xor 24 18 23, xnor 25 10 6, and 26 5 25,
  xor 27 14 26, and 28 4 27, xor 29 20 28,
  xnor 30 9 6, and 31 1 8, xor 32 7 31,
  and 33 5 32, xor 34 30 33, and 35 4 13,
  xor 36 34 35, and 37 2 36, xor 38 29 37,
  and 39 0 38, xor 40 24 39, and 41 5 31,
  xor 42 14 41, xnor 43 33 6, and 44 4 43,
  xor 45 42 44, xor 46 31 33, xor 47 3 15,
  and 48 4 47, xor 49 46 48, and 50 2 49,
  xor 51 45 50, xnor 52 38 6, and 53 0 52,
  xor 54 51 53, xor 55 10 33, and 56 4 8,
  xor 57 55 56, xor 58 1 48, and 59 2 58,
  xor 60 57 59, xnor 61 42 6, xor 62 32 41,
  and 63 4 62, xor 64 61 63, xor 65 19 11,
  xor 66 65 35, and 67 2 66, xor 68 64 67,
  and 69 0 68, xor 70 60 69, xor 71 31 5,
  xor 72 3 31, xor 73 72 41, and 74 4 73,
  xor 75 71 74, xnor 76 11 6, xor 77 76 21,
  and 78 2 77, xor 79 75 78, xnor 80 68 6,
  and 81 0 80, xor 82 79 81]

def outputs3 : List Nat := [40, 54, 70, 82]

def box4 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 3 6,
  and 9 8 5, xor 10 7 9, xnor 11 0 6,
  and 12 11 10, xor 13 5 12, xnor 14 5 6,
  and 15 8 14, xor 16 14 15, xnor 17 4 6,
  and 18 17 16, xor 19 13 18, xor 20 14 9,
  and 21 17 20, xor 22 3 21, xnor 23 2 6,
  and 24 23 22, xor 25 19 24, and 26 11 14,
  xor 27 8 26, xor 28 5 8, and 29 11 9,
  xor 30 28 29, and 31 17 30, xor 32 27 31,
  xnor 33 16 6, and 34 11 33, xor 35 14 11,
  and 36 17 35, xor 37 34 36, and 38 23 37,
  xor 39 32 38, xnor 40 1 6, and 41 40 39,
  xor 42 25 41, and 43 11 16, xor 44 10 43,
  xor 45 44 17, xnor 46 15 6, and 47 11 46,
  xor 48 7 47, and 49 11 15, and 50 17 49,
  xor 51 48 50, and 52 23 51, xor 53 45 52,
  xor 54 20 49, and 55 17 54, xor 56 3 55,
  and 57 11 5, xor 58 14 57, and 59 17 58,
  xor 60 47 59, and 61 23 60, xor 62 56 61,
  and 63 40 62, xor 64 53 63, xor 65 16 11,
  xor 66 65 17, xor 67 46 43, xor 68 28 47,
  and 69 17 68, xor 70 67 69, and 71 23 70,
  xor 72 66 71, xnor 73 28 6, and 74 11 73,
  xor 75 16 74, and 76 23 75, xor 77 10 76,
  and 78 40 77, xor 79 72 78, xor 80 8 47,
  and 81 17 13, xor 82 80 81, xor 83 20 11,
  and 84 17 83, xor 85 58 84, and 86 23 85,
  xor 87 82 86, xor 88 73 12, and 89 11 3,
  xor 90 28 89, and 91 17 90, xor 92 88 91,
  xnor 93 20 6, xor 94 93 74, xnor 95 57 6,
  and 96 17 95, xor 97 94 96, and 98 23 97,
  xor 99 92 98, and 100 40 99, xor 101 87 100]

def outputs4 : List Nat := [42, 64, 79, 101]

def box5 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 4 6,
  and 9 3 8, xor 10 9 1, xor 11 4 9,
  and 12 1 3, xor 13 11 12, and 14 2 13,
  xor 15 10 14, xnor 16 12 6, xnor 17 3 6,
  and 18 1 17, xor 19 3 18, and 20 2 19,
  xor 21 16 20, and 22 5 21, xor 23 15 22,
  xor 24 8 3, and 25 1 24, xor 26 9 25,
  and 27 2 26, and 28 3 4, xor 29 8 28,
  xnor 30 24 6, xor 31 30 25, and 32 2 31,
  xor 33 29 32, and 34 5 33, xor 35 27 34,
  and 36 0 35, xor 37 23 36, and 38 1 9,
  xor 39 28 38, and 40 1 4, xor 41 7 40,
  and 42 2 41, xor 43 39 42, xor 44 11 18,
  and 45 2 40, xor 46 44 45, and 47 5 46,
  xor 48 43 47, and 49 2 1, xor 50 41 49,
  xor 51 17 38, and 52 1 8, and 53 2 52,
  xor 54 51 53, and 55 5 54, xor 56 50 55,
  and 57 0 56, xor 58 48 57, xor 59 24 18,
  xor 60 8 12, and 61 2 60, xor 62 59 61,
  xnor 63 9 6, and 64 1 28, xor 65 63 64,
  and 66 2 25, xor 67 65 66, and 68 5 67,
  xor 69 62 68, xnor 70 45 6, xor 71 9 38,
  xor 72 28 1, and 73 2 72, xor 74 71 73,
  and 75 5 74, xor 76 70 75, and 77 0 76,
  xor 78 69 77, xor 79 29 1, xor 80 79 20,
  and 81 5 19, xor 82 80 81, xor 83 63 18,
  and 84 2 83, xor 85 19 84, and 86 1 63,
  xor 87 63 86, xor 88 29 52, and 89 2 88,
  xor 90 87 89, and 91 5 90, xor 92 85 91,
  and 93 0 92, xor 94 82 93]

def outputs5 : List Nat := [37, 58, 78, 94]

def box6 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xor 8 5 0,
  and 9 0 5, and 10 2 9, xor 11 8 10,
  xnor 12 9 6, and 13 2 12, xor 14 7 13,
  and 15 3 14, xor 16 11 15, xnor 17 5 6,
  and 18 0 17, and 19 2 18, xor 20 7 19,
  and 21 3 12, xor 22 20 21, and 23 4 22,
  xor 24 16 23, and 25 3 13, xor 26 14 25,
  and 27 2 0, xor 28 9 27, and 29 4 28,
  xor 30 26 29, and 31 1 30, xor 32 24 31,
  xor 33 9 2, xnor 34 8 6, xor 35 34 19,
  and 36 3 35, xor 37 33 36, and 38 2 5,
  xor 39 7 38, xor 40 5 9, xor 41 40 19,
  and 42 3 41, xor 43 39 42, and 44 4 43,
  xor 45 37 44, xor 46 17 18, xnor 47 0 6,
  and 48 2 47, xor 49 46 48, xor 50 49 42,
  and 51 2 34, and 52 3 40, xor 53 51 52,
  and 54 4 53, xor 55 50 54, and 56 1 55,
  xor 57 45 56, xnor 58 40 6, and 59 2 17,
  xor 60 58 59, and 61 3 5, xor 62 60 61,
  xor 63 34 13, xor 64 12 38, and 65 3 64,
  xor 66 63 65, and 67 4 66, xor 68 62 67,
  and 69 2 8, and 70 3 69, xor 71 7 70,
  and 72 4 19, xor 73 71 72, and 74 1 73,
  xor 75 68 74, xor 76 18 38, xor 77 76 21,
  xor 78 5 59, and 79 2 46, xor 80 46 79,
  and 81 3 80, xor 82 78 81, and 83 4 82,
  xor 84 77 83, xor 85 58 10, xor 86 5 79,
  and 87 3 86, xor 88 85 87, xor 89 38 61,
  and 90 4 89, xor 91 88 90, and 92 1 91,
  xor 93 84 92]

def outputs6 : List Nat := [32, 57, 75, 93]

def box7 : List Gate := [
  xor 6 0 0, xnor 7 0 0, xnor 8 0 6,
  xor 9 5 8, xnor 10 3 6, xor 11 9 10,
  xnor 12 1 6, xor 13 11 12, and 14 10 0,
  and 15 8 5, and 16 10 15, xor 17 8 16,
  and 18 12 17, xor 19 14 18, xnor 20 4 6,
  and 21 20 19, xor 22 13 21, xnor 23 5 6,
  and 24 8 23, xor 25 7 24, xor 26 25 14,
  and 27 12 26, xor 28 8 27, xor 29 5 15,
  and 30 10 29, xor 31 7 30, and 32 12 23,
  xor 33 31 32, and 34 20 33, xor 35 28 34,
  xnor 36 2 6, and 37 36 35, xor 38 22 37,
  xnor 39 15 6, xor 40 39 30, xnor 41 29 6,
  and 42 10 41, xor 43 23 42, and 44 12 43,
  xor 45 40 44, xnor 46 16 6, and 47 12 16,
  xor 48 46 47, and 49 20 48, xor 50 45 49,
  xor 51 5 24, xor 52 51 14, and 53 12 9,
  xor 54 52 53, xnor 55 52 6, xnor 56 51 6,
  and 57 12 56, xor 58 55 57, and 59 20 58,
  xor 60 54 59, and 61 36 60, xor 62 50 61,
  xor 63 24 16, and 64 10 39, xor 65 5 64,
  and 66 12 65, xor 67 63 66, xor 68 39 42,
  and 69 20 68, xor 70 67 69, xor 71 39 32,
  xor 72 15 16, xor 73 72 32, and 74 20 73,
  xor 75 71 74, and 76 36 75, xor 77 70 76,
  and 78 12 46, xor 79 65 78, and 80 10 24,
  xor 81 15 80, xor 82 0 30, and 83 12 82,
  xor 84 81 83, and 85 20 84, xor 86 79 85,
  xor 87 25 53, xnor 88 81 6, and 89 12 41,
  xor 90 88 89, and 91 20 90, xor 92 87 91,
  and 93 36 92, xor 94 86 93]

def outputs7 : List Nat := [38, 62, 77, 94]

def gates (i : Nat) : List Gate :=
  match i with
  | 0 => box0
  | 1 => box1
  | 2 => box2
  | 3 => box3
  | 4 => box4
  | 5 => box5
  | 6 => box6
  | _ => box7

def outputs (i : Nat) : List Nat :=
  match i with
  | 0 => outputs0
  | 1 => outputs1
  | 2 => outputs2
  | 3 => outputs3
  | 4 => outputs4
  | 5 => outputs5
  | 6 => outputs6
  | _ => outputs7

end VG.Impl.TripleDes.Circuit
