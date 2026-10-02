import VerifiedGarbage.Proof.Argon2.X86_64.DeriveReturn
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveMxcsr

/-! Functional correctness, termination, memory safety, and the complete System V ABI. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem code_correct (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    ∃ tr t, Exec isa (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) s tr t ∧
      abiPreserved s t ∧ (Spec.Argon2.deriveContract X86_64.abi 344).post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := code_wp v name s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (code_mxcsr v name) run ⟨regs, ?_⟩, post⟩
  have h := abi_environment s pre
  apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [wholeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.reserved _ (by simp) (abiMatrix s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiWork s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiOutput s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.Derive
