import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.Stream
import VerifiedGarbage.Impl.Sha1.X86_64.Stream

/-!
# Streaming SHA-1 on x86-64: `init`
-/

namespace VG.Proof.Sha1.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha1.X86_64.Stream
open VG.Impl.Sha1.X86_64 (at_)
open VG.Proof.Sha1.X86_64 (ea_at contains_offset' writeState stateAt_writeState)

/-! ## `init` -/

theorem init_eq : init = .block [
    .mov32 .rax (.imm 0x67452301), .store32 (at_ .rdi (4 * 0)) .rax,
    .mov32 .rax (.imm 0xefcdab89), .store32 (at_ .rdi (4 * 1)) .rax,
    .mov32 .rax (.imm 0x98badcfe), .store32 (at_ .rdi (4 * 2)) .rax,
    .mov32 .rax (.imm 0x10325476), .store32 (at_ .rdi (4 * 3)) .rax,
    .mov32 .rax (.imm 0xc3d2e1f0), .store32 (at_ .rdi (4 * 4)) .rax] := rfl

theorem init_post {s₀ : State}
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 84⟩) (g : Reg → BitVec 64)
    (hg : ∀ r, r ≠ .rax → g r = s₀.gpr r) :
    gprPreserved s₀ { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Sha1.H0 } ∧
      Proof.Sha1.initX86_64.post s₀
        { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Sha1.H0 } := by
  have hf : Frame [⟨s₀.gpr .rdi, 84⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) Spec.Sha1.H0) := by
    have c : ∀ k, k < 5 → (⟨s₀.gpr .rdi, 84⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
      fun k hk => contains_offset' (by omega) (by omega)
    simp only [writeState]
    refine ((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, Stream.repr_nil (stateAt_writeState _ _ _)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)

set_option simprocs false in
theorem init_correct {s₀ : State} (hp : Proof.Sha1.initX86_64.pre s₀) :
    WP isa init s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha1.initX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ k, k < 5 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .rdi, 84⟩, by simp [hwr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 0 (by omega); have o1 := o 1 (by omega); have o2 := o 2 (by omega)
  have o3 := o 3 (by omega); have o4 := o 4 (by omega)
  rw [init_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.store32,
    State.setReg32, State.setReg, o0, o1, o2, o3, o4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact init_post hret _ fun r hr => by simp [hr]

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 84⟩]

theorem init_verified : Verified X86_64.target init Proof.Sha1.initX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.X86_64.Stream
