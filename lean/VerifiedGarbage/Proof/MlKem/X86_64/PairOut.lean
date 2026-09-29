import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts

/-!
# ML-KEM on x86-64: loops that write a polynomial two coefficients at a time

Untrusted: everything here is checked by Lean. A loop that reads its
input through `rdi`, `d` bytes per iteration, and writes coefficients
`2i` and `2i + 1` of the polynomial at `rsi` in iteration `i` (`PairInv`),
one step further (`PairInv.step`), and its end (`PairInv.polyIs`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.MlKem

/-- After `i` iterations, from the input at `inP` and to the polynomial at
`outP`, whose first `2i` coefficients are `val 0, …`. -/
structure PairInv (s₀ : State) (inP outP : Addr) (d : Nat) (val : Nat → Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = inP + BitVec.ofNat 64 (d * i)
  rsi : s.gpr .rsi = outP + BitVec.ofNat 64 (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR outP] s₀.mem s.mem
  done : ∀ k < 2 * i, (coeffAt s.mem outP k).toNat = val k

namespace PairInv

variable {s₀ : State} {inP outP : Addr} {d : Nat} {val : Nat → Nat}

theorem init {s : State} (hm : s.mem = s₀.mem) (hk : Keep [.rcx] s₀ s) (hdi : s₀.gpr .rdi = inP)
    (hsi : s₀.gpr .rsi = outP) : PairInv s₀ inP outP d val 0 s :=
  ⟨by rw [hk.gpr (by decide), hdi]; simp, by rw [hk.gpr (by decide), hsi]; simp, hk.2.1, hk.2.2,
    by rw [hm]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩

theorem addr0 {i : Nat} {s : State} (hI : PairInv s₀ inP outP d val i s) :
    s.gpr .rsi = coeffAddr outP (2 * i) := by
  rw [hI.rsi]; congr 2; omega

theorem addr1 {i : Nat} {s : State} (hI : PairInv s₀ inP outP d val i s) :
    s.gpr .rsi + BitVec.ofNat 64 4 = coeffAddr outP (2 * i + 1) := by
  rw [hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-- The iteration that writes `x` and `y`. -/
theorem step {i : Nat} (hi : i < 128) {s s' : State} (hI : PairInv s₀ inP outP d val i s)
    {x y : BitVec 32} (hx : x.toNat = val (2 * i)) (hy : y.toNat = val (2 * i + 1))
    (hm : s'.mem = (s.mem.writeW (coeffAddr outP (2 * i)) x).writeW (coeffAddr outP (2 * i + 1)) y)
    (hdi : s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 d) (hsi : s'.gpr .rsi = s.gpr .rsi + 8)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : PairInv s₀ inP outP d val (i + 1) s' := by
  refine ⟨?_, ?_, hrd.trans hI.rd, hwr.trans hI.wr, ?_, fun k hk' => ?_⟩
  · rw [hdi, hI.rdi]; exact ptr_step _ i d
  · rw [hsi, hI.rsi]; exact ptr_step _ i 8
  · rw [hm]
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * i < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * i + 1 < 256 by omega))
  · rw [hm, coeffAt_writeW _ _ (show k < 256 by omega) (show 2 * i + 1 < 256 by omega),
      coeffAt_writeW _ _ (show k < 256 by omega) (show 2 * i < 256 by omega)]
    by_cases h1 : 2 * i + 1 = k
    · subst h1; rw [ifp rfl]; exact hy
    · rw [ifn h1]
      by_cases h0 : 2 * i = k
      · subst h0; rw [ifp rfl]; exact hx
      · rw [ifn h0]; exact hI.done k (by omega)

/-- At the end, the polynomial. -/
theorem polyIs {f : Poly} {s : State} (hI : PairInv s₀ inP outP d val 128 s)
    (hv : ∀ k < 256, val k = (f[k]!).val) : PolyIs s.mem outP f :=
  polyIs_of_toNat fun k hk => (hI.done k (by omega)).trans (hv k hk)

end PairInv

end VG.Proof.MlKem.X86_64
