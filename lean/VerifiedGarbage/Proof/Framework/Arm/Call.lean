import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# Calls (ARMv7)

Untrusted: everything here is checked by Lean.

A call (`Code.call`, `bl`) leaves the return address in `lr` and an unknown
value in `r12` (a linker veneer's), and runs the called function from there
(`State.callEntry`); it does not touch the stack. `WP.call` runs a call of
verified code from the callee's `Verified` proof, as `WP.inline` does for
inlined code.
-/

namespace VG.Arm

/-- The state a call enters the callee in. -/
def State.callEntry (s : State) : State :=
  { (s.setReg .lr (s.unknowns 0)).setReg .r12 (s.unknowns 1) with unknowns := fun n => s.unknowns (n + 2) }

theorem call_callEntry (s : State) : isa.call s = some s.callEntry := rfl

@[simp] theorem State.callEntry_rd (s : State) : s.callEntry.rd = s.rd := rfl
@[simp] theorem State.callEntry_wr (s : State) : s.callEntry.wr = s.wr := rfl
@[simp] theorem State.callEntry_sp (s : State) : s.callEntry.sp = s.sp := rfl
@[simp] theorem State.callEntry_mem (s : State) : s.callEntry.mem = s.mem := rfl

theorem State.callEntry_gpr (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  (call_eq (call_callEntry s)).2.2.2.2 r h

/-- Calls change none of the callee-saved registers but `lr`. -/
theorem preserved_not_link : ∀ r ∈ preserved, r ≠ .lr → r ∉ linkRegs := by decide

/-- A call of verified code without calls of its own: from a state `s` in
which the callee's precondition holds on entry, with its permissions narrowed
to `rd` and `wr`, the call returns in a state that has the permissions and
stack pointer of `s`, its callee-saved registers but `lr`, and every register
other than `lr` and `r12` that the callee's instructions never write; that
differs from `s` in memory only within `wr`; and that satisfies the callee's
postcondition (on the narrowed states). -/
theorem WP.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      (∀ r, (∀ i ∈ instrs c, dstOf i ≠ some r) → r ∉ linkRegs → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he (Code.noFrames_of_noCalls hn)
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    have h := habi.1 .lr (by decide)
    simp only [State.withRegions_gpr] at h
    simp only [isa, ret, State.withRegions_gpr, h, ite_true]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl habi.2 hf (fun r hr' hlr => ?_)
    (fun r hr' hl => ?_) ?_⟩
  · simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s (preserved_not_link r hr' hlr)]
  · rw [Exec.gpr hr' he' (.inl hn), State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

end VG.Arm
