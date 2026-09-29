import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Impl.Sha512.X86_64.Stream

/-!
# Streaming SHA-512 on x86-64: `init`

Untrusted: everything here is checked by Lean. One proof for every initial
hash value `iv`.
-/

namespace VG.Proof.Sha512.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Stream
open VG.Impl.Sha512.X86_64 (at_)
open VG.Proof.Sha512.X86_64 (ea_at contains_offset' writeState stateAt_writeState)
open VG.Spec.Sha512 (HashValue)

/-! ## `init` -/

theorem init_eq (iv : HashValue) : init iv = .block [
    .movImm64 .rax iv[0], .store (at_ .rdi (8 * 0)) .rax,
    .movImm64 .rax iv[1], .store (at_ .rdi (8 * 1)) .rax,
    .movImm64 .rax iv[2], .store (at_ .rdi (8 * 2)) .rax,
    .movImm64 .rax iv[3], .store (at_ .rdi (8 * 3)) .rax,
    .movImm64 .rax iv[4], .store (at_ .rdi (8 * 4)) .rax,
    .movImm64 .rax iv[5], .store (at_ .rdi (8 * 5)) .rax,
    .movImm64 .rax iv[6], .store (at_ .rdi (8 * 6)) .rax,
    .movImm64 .rax iv[7], .store (at_ .rdi (8 * 7)) .rax] := rfl

theorem init_post {s₀ : State} (iv : HashValue)
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 192⟩) (g : Reg → BitVec 64)
    (hg : ∀ r, r ≠ .rax → g r = s₀.gpr r) :
    gprPreserved s₀ { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) iv } ∧
      (Proof.Sha512.initX86_64 iv).post s₀
        { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) iv } := by
  have hf : Frame [⟨s₀.gpr .rdi, 192⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) iv) := by
    have c : ∀ k, k < 8 → (⟨s₀.gpr .rdi, 192⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((8 * k : Nat) : Int)) (64 / 8) :=
      fun k hk => contains_offset' (by omega) (by omega)
    simp only [writeState]
    refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
      (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, Stream.repr_nil (stateAt_writeState _ _ _)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)

set_option simprocs false in
theorem init_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha512.initX86_64 iv).pre s₀) :
    WP isa (init iv) s₀ fun s' => gprPreserved s₀ s' ∧ (Proof.Sha512.initX86_64 iv).post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
    fun k hk => ⟨⟨s₀.gpr .rdi, 192⟩, by simp [hwr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 0 (by omega); have o1 := o 1 (by omega); have o2 := o 2 (by omega)
  have o3 := o 3 (by omega); have o4 := o 4 (by omega); have o5 := o 5 (by omega)
  have o6 := o 6 (by omega); have o7 := o 7 (by omega)
  rw [init_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, ea_at, State.store64,
    State.setReg, o0, o1, o2, o3, o4, o5, o6, o7, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  exact init_post iv hret _ fun r hr => by simp [hr]

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
  wr := [⟨0x1000, 192⟩]

/-- The hint for `init 0`, which is also one for `init iv`. -/
abbrev initHint : VG.Taint.Hint taint.T := VG.Taint.hintOf taint (Taint.ofRegs [.rdi]) (init 0)

/-- The taint check never looks at an immediate, so its result on `init iv`
is its result on `init 0`, which is decided. -/
theorem init_check (iv : HashValue) :
    (taint.check (Taint.ofRegs [.rdi]) (init iv) initHint).isSome = true := by
  have h : (taint.check (Taint.ofRegs [.rdi]) (init 0) initHint).isSome = true := by decide +kernel
  rw [show taint.check (Taint.ofRegs [.rdi]) (init iv) initHint =
    taint.check (Taint.ofRegs [.rdi]) (init 0) initHint from rfl]
  exact h

theorem init_verified (iv : HashValue) :
    Verified X86_64.target (init iv) (Proof.Sha512.initX86_64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    refine ⟨t, s', he, abiPreserved_of_exec ?_ he h.1, h.2⟩
    rw [show (init iv).allInstrs (fun i => !loadsMxcsr i) =
      (init 0).allInstrs (fun i => !loadsMxcsr i) from rfl]
    decide +kernel
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (init_check iv)
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · intro a h₁ h₂
    simp only [Region.Contains, initSat] at h₁ h₂
    bv_omega

end VG.Proof.Sha512.X86_64.Stream
