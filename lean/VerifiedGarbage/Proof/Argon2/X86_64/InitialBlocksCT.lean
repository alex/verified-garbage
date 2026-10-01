import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Constant time of H₀ header and input argument preparation

Only frame and scratch addresses affect these blocks' execution traces.
The relational proof of the complete derivation additionally tracks public
lengths and pointers across its BLAKE2b calls.
-/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

def AgreeBases (s t : State) : Prop := s.gpr .rbp = t.gpr .rbp ∧ s.gpr .rbx = t.gpr .rbx

theorem agreeBases_taint {s t : State} (h : AgreeBases s t) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rbp, .rbx]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem header_rel : RelCT isa AgreeBases headerCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => agreeBases_taint h) (by taint_decide)

theorem lengthArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp, .rbx])
      (.block (lengthArgs offset)) hint).isSome = true) :
    RelCT isa AgreeBases (.block (lengthArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .rbx])
    (fun _ _ h => agreeBases_taint h) check

theorem inputArgs_rel (offset : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs [.rbp])
      (.block (inputArgs offset)) hint).isSome = true) :
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs offset)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)) check

/-- All four concrete input blocks use their checked public base address. -/
theorem inputs_rel :
    RelCT isa AgreeBases (.block (lengthArgs passwordLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs saltLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs secretLenOffset)) (fun _ _ => True) ∧
    RelCT isa AgreeBases (.block (lengthArgs adLenOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs passwordOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs saltOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs secretOffset)) (fun _ _ => True) ∧
    RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
      (.block (inputArgs adOffset)) (fun _ _ => True) :=
  ⟨lengthArgs_rel _ ⟨_, by taint_decide⟩, lengthArgs_rel _ ⟨_, by taint_decide⟩,
    lengthArgs_rel _ ⟨_, by taint_decide⟩, lengthArgs_rel _ ⟨_, by taint_decide⟩,
    inputArgs_rel _ ⟨_, by taint_decide⟩, inputArgs_rel _ ⟨_, by taint_decide⟩,
    inputArgs_rel _ ⟨_, by taint_decide⟩, inputArgs_rel _ ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.X86_64.Initial
