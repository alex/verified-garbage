import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Carry

/-!
# X25519 on x86-64 with AVX512_IFMA: the stages' operands

The blocks between the carries and the products of an iteration, run
symbolically: each output limb, lane by lane, as a number (`rfl`), and its
bounds (`decide`).
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- A block run from its start. -/
def symOf (is : List Instr) (h : (Sym.init.run is).isSome := by decide +kernel) : Sym :=
  (Sym.init.run is).get h

theorem symOf_eq (is : List Instr) (h : (Sym.init.run is).isSome) :
    Sym.init.run is = some (symOf is h) := (Option.some_get _).symm

/-! ## Stage 1 -/

def s1a : Sym := symOf stage1a

/-- `(x₂ + z₂, x₂ + bias - z₂, x₃ + z₃, x₃ + bias - z₃)`, limb `j`. -/
def s1aNat (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 0 + E.v j 1
  | 1 => E.v j 0 + (E.m (kb j) 1 - E.v j 1)
  | 2 => E.v j 2 + E.v j 3
  | _ => E.v j 2 + (E.m (kb j) 3 - E.v j 3)

theorem s1a_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s1a.reg j).nat E l = s1aNat E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Bounds: limbs below `2⁶¹`, and the bias. -/
def s1aB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem s1a_ok : ∀ j < 5, ∀ l < 4, (s1a.reg j).ok s1aB l = true ∧ (s1a.reg j).bnd s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s1a_keep : ∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → s1a.reg r = .reg r := by decide +kernel
theorem s1a_st : s1a.st = [] := by decide +kernel

def s1b : Sym := symOf stage1b

theorem s1b_regs : ∀ j < 5, s1b.reg (5 + j) = .perm (.reg j) (ord 0 1 0 1).toNat := by decide +kernel
theorem s1b_st : s1b.st = [(OPL + 128, .perm (.reg 4) (ord 0 1 3 2).toNat),
    (OPL + 96, .perm (.reg 3) (ord 0 1 3 2).toNat), (OPL + 64, .perm (.reg 2) (ord 0 1 3 2).toNat),
    (OPL + 32, .perm (.reg 1) (ord 0 1 3 2).toNat), (OPL, .perm (.reg 0) (ord 0 1 3 2).toNat)] := by
  decide +kernel
theorem s1b_keep : ∀ r < 16, (r < 5 ∨ 11 ≤ r) → s1b.reg r = .reg r := by decide +kernel

/-! ## Stage 2 -/

def s2a : Sym := symOf stage2a

/-- `(DA + CB, DA + bias - CB, AA, AA + bias - BB)`, limb `j`. -/
def s2aV (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2 + E.v j 3
  | 1 => E.v j 2 + (E.m (kb j) 1 - E.v j 3)
  | 2 => E.v j 0 + 0
  | _ => E.v j 0 + (E.m (kb j) 3 - E.v j 1)

/-- `(DA + CB, DA + bias - CB, BB, a24)`, limb `j`. -/
def s2aW (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2 + E.v j 3
  | 1 => E.v j 2 + (E.m (kb j) 1 - E.v j 3)
  | 2 => E.v j 1
  | _ => E.m (KA24 + 32 * j) 3

theorem s2a_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (s2a.reg (5 + j)).nat E l = s2aV E j l ∧ (s2a.reg j).nat E l = s2aW E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Bounds: products below `2⁶¹`, the bias, and `a24`'s slot. -/
def s2aB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048
      else if KA24 ≤ d ∧ d < KA24 + 160 ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem s2a_ok : ∀ j < 5, ∀ l < 4, (s2a.reg (5 + j)).ok s2aB l = true ∧
    (s2a.reg (5 + j)).bnd s2aB l < 2 ^ 63 ∧ (s2a.reg j).ok s2aB l = true ∧
    (s2a.reg j).bnd s2aB l < 2 ^ 63 := by
  decide +kernel

theorem s2a_keep : ∀ r < 16, 14 ≤ r → s2a.reg r = .reg r := by decide +kernel
theorem s2a_st : s2a.st = [] := by decide +kernel

def s2b : Sym := symOf stage2b

theorem s2b_regs : ∀ j < 5, s2b.reg (5 + j) = .reg j := by decide +kernel
theorem s2b_st : s2b.st = [(OPV + 128, .reg 9), (OPV + 96, .reg 8), (OPV + 64, .reg 7),
    (OPV + 32, .reg 6), (OPV, .reg 5)] := by decide +kernel
theorem s2b_keep : ∀ r < 16, (r < 5 ∨ 10 ≤ r) → s2b.reg r = .reg r := by decide +kernel

/-! ## Stage 3 -/

def s3a : Sym := symOf stage3a

/-- `(1, AA + a24 E, 1, x₁)`, limb `j` (the constants from `KX1`). -/
def s3aH (E : Env) (j : Nat) : Nat → Nat
  | 1 => E.m (OPV + 32 * j) 2 + E.v j 3
  | l => E.m (KX1 + 32 * j) l

/-- `(x₂', E, x₃', t)`, limb `j`. -/
def s3aG (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 2
  | 1 => E.m (OPV + 32 * j) 3
  | 2 => E.v j 0
  | _ => E.v j 1

theorem s3a_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (s3a.reg (5 + j)).nat E l = s3aH E j l ∧ (s3a.reg j).nat E l = s3aG E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Bounds: products below `2⁶¹`, stage 2's first operand and `x₁`'s slot
below `2⁵²`. -/
def s3aB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if ((OPV ≤ d ∧ d < OPV + 160) ∨ (KX1 ≤ d ∧ d < KX1 + 160)) ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1,
    fun _ => 0⟩

theorem s3a_ok : ∀ j < 5, ∀ l < 4, (s3a.reg (5 + j)).ok s3aB l = true ∧
    (s3a.reg (5 + j)).bnd s3aB l < 2 ^ 63 ∧ (s3a.reg j).ok s3aB l = true ∧
    (s3a.reg j).bnd s3aB l < 2 ^ 63 := by
  decide +kernel

theorem s3a_keep : ∀ r < 16, 13 ≤ r → s3a.reg r = .reg r := by decide +kernel
theorem s3a_st : s3a.st = [] := by decide +kernel

def s3b : Sym := symOf stage3b

theorem s3b_st : s3b.st = [(OPG + 128, .reg 4), (OPG + 96, .reg 3), (OPG + 64, .reg 2),
    (OPG + 32, .reg 1), (OPG, .reg 0)] := by decide +kernel
theorem s3b_keep : ∀ r < 16, s3b.reg r = .reg r := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma
