import VerifiedGarbage.Proof.X448.X86.Main
import VerifiedGarbage.Proof.X448.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is a pointer plus a constant or the counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [56, 8192], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X448.x448X86.pre s₁) (h₂ : Proof.X448.x448X86.pre s₂)
    (hpub : Proof.X448.x448X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem x448_ct : ConstantTime isa Proof.X448.x448X86.pre Proof.X448.x448X86.pub
    Impl.X448.X86.x448 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448X86.pre s) :
    ∃ t s', Exec isa Impl.X448.X86.x448 s t s' ∧ abiPreserved s s' ∧ Proof.X448.x448X86.post s s' :=
  correct (Pre.of s hs)

theorem x448_verified :
    Verified X86.target Impl.X448.X86.x448 (Spec.X448.x448Contract X86.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have a2 : arg satState 2 = 0x3000 := by decide
    have a3 : arg satState 3 = 0x4000 := by decide
    have e : argAddr satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.x448X86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, e, esp] using Proof.X448.X86.satState)

end VG.Proof.X448.X86
