import VerifiedGarbage.Proof.Md5.X86_64.Stream.Common

/-!
# Streaming MD5 on x86-64: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Md5.X86_64.Stream

open VG VG.X86_64 VG.Impl.Md5.X86_64.Stream
open VG.Impl.Md5.X86_64 (at_)
open VG.Proof.Md5.X86_64 (ea_at contains_offset' writeState stateAt_writeState)

/-! ## `init` -/

theorem init_eq : init = .block [
    .mov32 .rax (.imm 0x67452301), .store32 (at_ .rdi (4 * 0)) .rax,
    .mov32 .rax (.imm 0xefcdab89), .store32 (at_ .rdi (4 * 1)) .rax,
    .mov32 .rax (.imm 0x98badcfe), .store32 (at_ .rdi (4 * 2)) .rax,
    .mov32 .rax (.imm 0x10325476), .store32 (at_ .rdi (4 * 3)) .rax] := rfl

theorem init_post {s₀ : State}
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 80⟩) (g : Reg → BitVec 64)
    (hg : ∀ r, r ≠ .rax → g r = s₀.gpr r) :
    abiPreserved s₀ { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Md5.H0 } ∧
      Proof.Md5.initX86_64.post s₀
        { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) Spec.Md5.H0 } := by
  have hf : Frame [⟨s₀.gpr .rdi, 80⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) Spec.Md5.H0) := by
    have c : ∀ k, k < 4 → (⟨s₀.gpr .rdi, 80⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
      fun k hk => contains_offset' (by omega) (by omega)
    simp only [writeState]
    refine (((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, Stream.repr_nil (stateAt_writeState _ _ _)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)

set_option simprocs false in
theorem init_correct {s₀ : State} (hp : Proof.Md5.initX86_64.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Md5.initX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ k, k < 4 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .rdi, 80⟩, by simp [hwr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 0 (by omega); have o1 := o 1 (by omega); have o2 := o 2 (by omega)
  have o3 := o 3 (by omega)
  rw [init_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.store32,
    State.setReg32, State.setReg, o0, o1, o2, o3, ite_true, ite_false,
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
  wr := [⟨0x1000, 80⟩]

theorem init_verified : Verified X86_64.target init Proof.Md5.initX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · intro a h₁ h₂
    simp only [Region.Contains, initSat] at h₁ h₂
    bv_omega

end VG.Proof.Md5.X86_64.Stream
