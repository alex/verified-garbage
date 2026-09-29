import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM on AArch64: what the proofs share

Untrusted: everything here is checked by Lean. Memory of zeros (for the
states that show a precondition satisfiable), the tactic that moves a
proof from a per-target contract to the shared one, and facts about the
registers a function never writes.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.MlKem

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

/-- A polynomial of zeros is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_zero]; decide

/-- `k.Implies k'` for `k'` built with `Sig.contract`, as `sig_implies`
proves it, where the satisfying state `w` may have preconditions on
polynomials of zeros (`reduced_zero`). -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _ _ ‹_›
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

/-- No instruction of `c` (without calls) writes a callee-saved register. -/
theorem preserved_of {c : Prog isa} (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) :
    ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps h) i hi) r hr
  simpa using this

/-- Code without calls that writes no callee-saved register, and keeps the
stack pointer, meets the calling convention. -/
theorem abi_of {c : Prog isa} (hc : c.noCalls = true)
    (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') : abiPreserved s s' :=
  ⟨fun r hr => Exec.gpr (preserved_of h r hr) he (.inl hc), Exec.sp he⟩

/-- Agreement on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.MlKem.AArch64
