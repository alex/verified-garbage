import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Reflect
import VerifiedGarbage.Proof.Sha3.Spec
import Mathlib.Tactic.IntervalCases

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

def Holds (reg : Nat → Reg) (A : Spec.Sha3.State) (f : File) : Prop :=
  ∀ i : Nat, (h : i < 25) → f.regs (reg i) = A[i]

def columnExpr (x : Nat) : Expr :=
  .xor (.xor (.xor (.xor (.reg (laneReg x)) (.reg (laneReg (x + 5))))
    (.reg (laneReg (x + 10)))) (.reg (laneReg (x + 15)))) (.reg (laneReg (x + 20)))

def thetaExpr (i : Nat) : Expr :=
  .xor (.reg (laneReg i)) (.xor (columnExpr ((i % 5 + 4) % 5))
    (.ror (columnExpr ((i % 5 + 1) % 5)) 63))

theorem theta_schedule : ∀ i < 25,
    (symRun thetaOps symInitial).regs (thetaReg i) = thetaExpr i := by decide +kernel

def rhoPiExpr (i : Nat) : Expr :=
  let j := Impl.Sha3.piSrc (i % 5) (i / 5)
  let k := Impl.Sha3.rhoOff j
  if k = 0 then .reg (thetaReg j) else .ror (.reg (thetaReg j)) (64 - k)

theorem rhoPi_schedule : ∀ i < 25,
    (symRun rhoPiOps symInitial).regs (laneReg i) = rhoPiExpr i := by decide +kernel

def chiExpr (i : Nat) : Expr :=
  let x := i % 5; let y := i / 5
  .xor (.reg (laneReg i))
    (.bic (.reg (laneReg ((x + 2) % 5 + 5 * y)))
      (.reg (laneReg ((x + 1) % 5 + 5 * y))))

theorem chi_schedule : ∀ i < 25,
    (symRun chiOps symInitial).regs (laneReg i) = chiExpr i := by decide +kernel

theorem columnExpr_eval (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f)
    (x : Nat) (hx : x < 5) :
    (columnExpr x).eval f = Proof.Sha3.C A x := by
  simp only [columnExpr, Expr.eval, h x (by omega), h (x + 5) (by omega),
    h (x + 10) (by omega), h (x + 15) (by omega), h (x + 20) (by omega),
    Proof.Sha3.C,
    Proof.Sha3.getElem!_eq (i := x) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 5) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 10) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 15) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 20) (hi := by omega)]

theorem theta_correct (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds thetaReg (Spec.Sha3.theta A) (run thetaOps f) := by
  intro i hi
  rw [run_regs, theta_schedule i hi]
  simp only [thetaExpr, Expr.eval, h i hi,
    columnExpr_eval A f h _ (Nat.mod_lt _ (by decide)), Proof.Sha3.theta_get A hi,
    Proof.Sha3.D, BitVec.xor_comm]

theorem rhoPiExpr_eval (f : File) (i : Nat) :
    (rhoPiExpr i).eval f =
      Proof.Sha3.rotl (f.regs (thetaReg (Impl.Sha3.piSrc (i % 5) (i / 5))))
        (Impl.Sha3.rhoOff (Impl.Sha3.piSrc (i % 5) (i / 5))) := by
  simp only [rhoPiExpr, Proof.Sha3.rotl]
  split <;> simp_all only [Expr.eval]

theorem rhoPi_correct (A : Spec.Sha3.State) (f : File) (h : Holds thetaReg A f) :
    Holds laneReg (Spec.Sha3.pi (Spec.Sha3.rho A)) (run rhoPiOps f) := by
  intro i hi
  have hx : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : i / 5 < 5 := by omega
  have hj : Impl.Sha3.piSrc (i % 5) (i / 5) < 25 := by
    simp only [Impl.Sha3.piSrc]; omega
  rw [run_regs, rhoPi_schedule i hi, rhoPiExpr_eval, h _ hj,
    Proof.Sha3.rotl_eq _ (Proof.Sha3.rhoOff_lt _ hj)]
  have hp := Proof.Sha3.pi_get (Spec.Sha3.rho A) hx hy
  have hp' : (Spec.Sha3.pi (Spec.Sha3.rho A))[i] =
      (Spec.Sha3.rho A)[Impl.Sha3.piSrc (i % 5) (i / 5)] := by
    simpa only [show i % 5 + 5 * (i / 5) = i by omega] using hp
  rw [hp', Proof.Sha3.rho_get A hj]

theorem chi_correct (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds laneReg (Spec.Sha3.chi A) (run chiOps f) := by
  intro i hi
  have hx : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : i / 5 < 5 := by omega
  have hn : (i % 5 + 1) % 5 + 5 * (i / 5) < 25 := by
    have := Nat.mod_lt (i % 5 + 1) (by decide : 0 < 5); omega
  have hn' : (i % 5 + 2) % 5 + 5 * (i / 5) < 25 := by
    have := Nat.mod_lt (i % 5 + 2) (by decide : 0 < 5); omega
  rw [run_regs, chi_schedule i hi]
  simp only [chiExpr, Expr.eval, h i hi, h _ hn, h _ hn']
  have hc := Proof.Sha3.chi_get A hx hy
  have hc' : (Spec.Sha3.chi A)[i] = A[i] ^^^
      (~~~A[(i % 5 + 1) % 5 + 5 * (i / 5)] &&&
        A[(i % 5 + 2) % 5 + 5 * (i / 5)]) := by
    simpa only [show i % 5 + 5 * (i / 5) = i by omega] using hc
  rw [hc', BitVec.and_comm]

end VG.Proof.Sha3.AArch64.Scalar
