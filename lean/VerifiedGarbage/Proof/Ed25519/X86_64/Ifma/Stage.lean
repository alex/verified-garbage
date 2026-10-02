import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Setup
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma

/-!
# Ed25519 doublings with AVX512_IFMA: the blocks, run symbolically

The vector blocks of `Ifma.double4` but X25519's products and carries, run
symbolically (`Proof/X25519/X86_64/Ifma/Sym.lean`): each output limb, lane by
lane, as a number (`rfl`), and its bounds (`decide`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds symOf limbNat)

/-! ## Loading slots 0–3 -/

def loadS : Sym := symOf vload

/-- Limb `j` of lane `l`: of slot `l`'s words. -/
theorem loadS_regs (E : Env) : ∀ j < 5, ∀ l < 4, (loadS.reg j).nat E l =
    limbNat (fun k => E.m (64 + 32 * l) k) (E.g .rax) j := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- The term `vload` stores at `d`. -/
def loadT (d : Nat) : T := ((loadS.st.find? fun x => x.1 == d).getD (0, .zero)).2

theorem loadT_mem : ∀ d ∈ [KM, K19, KB0, KB1, EK13, EK26, EK39], (d, loadT d) ∈ loadS.st := by
  decide +kernel

theorem loadT_const : ∀ x ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (EK13, .r8),
    (EK26, .r9), (EK39, .r10)], loadT x.1 = .bc (.lane0 (.gpr x.2)) := by decide +kernel

theorem loadS_small : ∀ x ∈ loadS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem loadS_apart : VG.Proof.X25519.X86_64.Ifma.Apart loadS.st := by decide +kernel
theorem loadS_range : ∀ x ∈ loadS.st, 1664 ≤ x.1 ∧ x.1 + 32 ≤ 1664 + 224 := by decide +kernel

def loadB : Bnds :=
  ⟨fun _ => 2 ^ 64 - 1, fun g => if g = .rax then 2 ^ 51 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun _ => 0⟩

theorem loadS_ok : ∀ j < 5, ∀ l < 4, (loadS.reg j).ok loadB l = true ∧ (loadS.reg j).bnd loadB l < 2 ^ 52 := by
  decide +kernel

/-! ## A doubling's first operands -/

def dblAS : Sym := symOf dblA

theorem dblAS_regs : ∀ j < 5, dblAS.reg (5 + j) = .perm (.reg j) (ord 0 1 2 1).toNat := by decide +kernel
theorem dblAS_st : dblAS.st = [(OPL + 128, .perm (.reg 4) (ord 0 1 2 0).toNat),
    (OPL + 96, .perm (.reg 3) (ord 0 1 2 0).toNat), (OPL + 64, .perm (.reg 2) (ord 0 1 2 0).toNat),
    (OPL + 32, .perm (.reg 1) (ord 0 1 2 0).toNat), (OPL, .perm (.reg 0) (ord 0 1 2 0).toNat)] := by
  decide +kernel
theorem dblAS_keep : ∀ r < 16, (r < 5 ∨ 11 ≤ r) → dblAS.reg r = .reg r := by decide +kernel

/-! ## A doubling's second operands -/

def dblBS : Sym := symOf dblB

/-- `F = 2C' + (A + bias - B)`, limb `j`, from `(A, B, C', P)` (`E.v j`). -/
def fNat (E : Env) (j : Nat) : Nat := E.v j 2 + E.v j 2 + (E.m (kb j) 0 + E.v j 0 - E.v j 1)

/-- `(E, G, F, E)`, limb `j`. -/
def dblOp1 (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 3 + E.v j 3
  | 1 => E.m (kb j) 1 + E.v j 1 - E.v j 0
  | 2 => fNat E j
  | _ => E.v j 3 + E.v j 3

/-- `(F, H, G, H)`, limb `j`. -/
def dblOp2 (E : Env) (j : Nat) : Nat → Nat
  | 0 => fNat E j
  | 1 => E.v j 0 + E.v j 1
  | 2 => E.m (kb j) 1 + E.v j 1 - E.v j 0
  | _ => E.v j 0 + E.v j 1

theorem dblBS_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (dblBS.reg j).nat E l = dblOp1 E j l ∧ (dblBS.reg (5 + j)).nat E l = dblOp2 E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The first product's limbs are below this. -/
def prodBound : Nat := 2 ^ 60 + 2 ^ 56

/-- Bounds: the first product's limbs, and the bias. -/
def dblBB : Bnds :=
  ⟨fun i => if i < 5 then prodBound - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem dblBS_ok : ∀ j < 5, ∀ l < 4, (dblBS.reg j).ok dblBB l = true ∧
    (dblBS.reg j).bnd dblBB l < 2 ^ 63 ∧ (dblBS.reg (5 + j)).ok dblBB l = true ∧
    (dblBS.reg (5 + j)).bnd dblBB l < 2 ^ 63 := by
  decide +kernel

theorem dblBS_keep : ∀ r < 16, 14 ≤ r → dblBS.reg r = .reg r := by decide +kernel
theorem dblBS_st : dblBS.st = [] := by decide +kernel

def dblCS : Sym := symOf dblC

theorem dblCS_st : dblCS.st = [(OPV + 128, .reg 4), (OPV + 96, .reg 3), (OPV + 64, .reg 2),
    (OPV + 32, .reg 1), (OPV, .reg 0)] := by decide +kernel
theorem dblCS_keep : ∀ r < 16, dblCS.reg r = .reg r := by decide +kernel

/-! ## Storing to slots 0–3 -/

/-- `vstore` after its carries. -/
def vpackE : List Instr := vstore.drop 34

theorem vstore_eq : vstore = VG.Impl.X25519.X86_64.Ifma.carry id ++
    VG.Impl.X25519.X86_64.Ifma.carry id ++ vpackE := by decide +kernel

def packS : Sym := symOf vpackE

theorem packS_st : packS.st.map Prod.fst = [160, 128, 96, 64] := by decide +kernel

/-- The term stored at `64 + 32 m`. -/
def packT (m : Nat) : T := ((packS.st.reverse).getD m (0, .zero)).2

theorem packT_mem : ∀ m < 4, (64 + 32 * m, packT m) ∈ packS.st := by decide +kernel

theorem packT_nat (E : Env) : ∀ m < 4, ∀ j < 4, (packT m).nat E j =
    VG.Proof.X25519.X86_64.Ifma.packW (fun i => E.v i m) (E.m KM m) (E.m EK13 m) (E.m EK26 m)
      (E.m EK39 m) j := by
  intro m hm j hj
  rcases VG.X86_64.cases4 hm with rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hj with rfl | rfl | rfl | rfl <;> rfl

def packB : Bnds :=
  ⟨fun r => if r < 5 then 2 ^ 51 + 18 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KM then 2 ^ 51 - 1 else if d = EK13 then 2 ^ 13 - 1 else if d = EK26 then 2 ^ 26 - 1
      else if d = EK39 then 2 ^ 39 - 1 else 2 ^ 64 - 1, fun _ => 0⟩

theorem packT_ok : ∀ m < 4, ∀ j < 4, (packT m).ok packB j = true := by decide +kernel

theorem packS_small : ∀ x ∈ packS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem packS_apart : VG.Proof.X25519.X86_64.Ifma.Apart packS.st := by decide +kernel

end VG.Proof.Ed25519.X86_64.Ifma
