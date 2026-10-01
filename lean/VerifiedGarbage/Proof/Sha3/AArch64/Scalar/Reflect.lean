import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

/-- Expressions preserve the meaning of the instruction schedule without
replaying its symbolic register writes once for every output lane. -/
inductive Expr where
  | reg (r : Reg)
  | slot (k : Nat)
  | xor (a b : Expr)
  | bic (a b : Expr)
  | ror (a : Expr) (n : Nat)
  deriving DecidableEq

def Expr.eval (f : File) : Expr → Lane
  | .reg r => f.regs r
  | .slot k => f.slots k
  | .xor a b => a.eval f ^^^ b.eval f
  | .bic a b => a.eval f &&& ~~~b.eval f
  | .ror a n => (a.eval f).rotateRight n

structure SymFile where
  regs : Reg → Expr
  slots : Nat → Expr

def SymFile.write (f : SymFile) (r : Reg) (v : Expr) : SymFile :=
  { f with regs := fun q => if q = r then v else f.regs q }

def symStep (f : SymFile) : ScalarOp → SymFile
  | .xor d a b => f.write d (.xor (f.regs a) (f.regs b))
  | .xorRor d a b n => f.write d (.xor (f.regs a) (.ror (f.regs b) n))
  | .bic d a b => f.write d (.bic (f.regs a) (f.regs b))
  | .bicRor d a b n => f.write d (.bic (f.regs a) (.ror (f.regs b) n))
  | .ror d a n => f.write d (.ror (f.regs a) n)
  | .move d a => f.write d (f.regs a)
  | .spill k a => { f with slots := fun j => if j = k then f.regs a else f.slots j }
  | .reload d k => f.write d (f.slots k)

def symRun (ops : List ScalarOp) (f : SymFile) : SymFile := ops.foldl symStep f

def symInitial : SymFile := ⟨Expr.reg, Expr.slot⟩

def Compatible (input : File) (sf : SymFile) (f : File) : Prop :=
  (∀ r, f.regs r = (sf.regs r).eval input) ∧
  (∀ k, f.slots k = (sf.slots k).eval input)

theorem symStep_correct (input f : File) (sf : SymFile) (op : ScalarOp)
    (h : Compatible input sf f) : Compatible input (symStep sf op) (step f op) := by
  obtain ⟨hr, hs⟩ := h
  cases op <;> constructor <;> intro q <;>
    simp only [step, symStep, File.write, SymFile.write]
  all_goals first | (split <;> simp_all only [Expr.eval]) | simp_all only

theorem symRun_correct (input f : File) (sf : SymFile) (ops : List ScalarOp)
    (h : Compatible input sf f) : Compatible input (symRun ops sf) (run ops f) := by
  induction ops generalizing f sf with
  | nil => exact h
  | cons op ops ih =>
    exact ih (step f op) (symStep sf op) (symStep_correct input f sf op h)

theorem run_regs (ops : List ScalarOp) (f : File) (r : Reg) :
    (run ops f).regs r = ((symRun ops symInitial).regs r).eval f :=
  (symRun_correct f f symInitial ops ⟨fun _ => rfl, fun _ => rfl⟩).1 r

end VG.Proof.Sha3.AArch64.Scalar
