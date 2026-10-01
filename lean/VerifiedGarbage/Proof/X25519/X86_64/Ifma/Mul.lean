import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound
import VerifiedGarbage.Impl.X25519.X86_64.Ifma

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw)

/-- The low halves of the products `a_i b_j` with `i + j = c`, summed as the
code does. -/
def accLo (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % 2 ^ 52 else acc) 0

/-- The high halves of the products `a_i b_j` with `i + j + 1 = c`. -/
def accHi (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / 2 ^ 52
    else acc) 0

/-- Limb `k` of `mul4`: column `k` plus 19 times column `k + 5`. -/
def mulNat (a b : Nat → Nat) (k : Nat) : Nat :=
  accLo a b k + accHi a b k * 2 ^ 1 + (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) +
    (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) * 2 ^ 1 +
    (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) * 2 ^ 4

def mulS (a : Nat) (h : (Sym.init.run (mul4 a)).isSome := by decide +kernel) : Sym :=
  (Sym.init.run (mul4 a)).get h

def mulB (a : Nat) : Bnds :=
  ⟨fun r => if 5 ≤ r ∧ r < 10 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if a ≤ d ∧ d < a + 160 ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 0⟩

theorem mulS_eq (a : Nat) (h : (Sym.init.run (mul4 a)).isSome) :
    Sym.init.run (mul4 a) = some (mulS a h) := (Option.some_get _).symm

def mulL : Sym := mulS OPL

theorem mulL_nat (E : Env) (l : Nat) : ∀ k < 5, (mulL.reg k).nat E l =
    mulNat (fun i => E.m (OPL + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulL_ok : ∀ k < 5, ∀ l < 4, (mulL.reg k).ok (mulB OPL) l = true ∧
    (mulL.reg k).bnd (mulB OPL) l < 2 ^ 61 := by decide +kernel

theorem mulL_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulL.reg r = .reg r := by decide +kernel
theorem mulL_st : mulL.st = [] := by decide +kernel

def mulV : Sym := mulS OPV

theorem mulV_nat (E : Env) (l : Nat) : ∀ k < 5, (mulV.reg k).nat E l =
    mulNat (fun i => E.m (OPV + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulV_ok : ∀ k < 5, ∀ l < 4, (mulV.reg k).ok (mulB OPV) l = true ∧
    (mulV.reg k).bnd (mulB OPV) l < 2 ^ 61 := by decide +kernel

theorem mulV_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulV.reg r = .reg r := by decide +kernel
theorem mulV_st : mulV.st = [] := by decide +kernel

def mulG : Sym := mulS OPG

theorem mulG_nat (E : Env) (l : Nat) : ∀ k < 5, (mulG.reg k).nat E l =
    mulNat (fun i => E.m (OPG + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulG_ok : ∀ k < 5, ∀ l < 4, (mulG.reg k).ok (mulB OPG) l = true ∧
    (mulG.reg k).bnd (mulB OPG) l < 2 ^ 61 := by decide +kernel

theorem mulG_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulG.reg r = .reg r := by decide +kernel
theorem mulG_st : mulG.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma
