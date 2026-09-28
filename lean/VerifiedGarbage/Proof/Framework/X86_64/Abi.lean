import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# x86-64: the calling-convention obligations

Untrusted: everything here is checked by Lean.

`abiPreserved` asks that MXCSR's control bits be restored. Code that never
loads MXCSR keeps it, so its proofs show only the other obligations
(`gprPreserved`), and `abiPreserved_of_exec` adds MXCSR's.
-/

namespace VG.X86_64

/-- Whether an instruction loads MXCSR. -/
def loadsMxcsr : Instr → Bool
  | .ldmxcsr _ => true
  | _ => false

theorem exec_mxcsr {i : Instr} (hi : loadsMxcsr i = false) {s s' : State} (h : exec i s = some s') :
    s'.mxcsr = s.mxcsr := by
  cases i with
  | ldmxcsr => cases hi
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | alu32 op d src =>
    simp only [exec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift32 op d n =>
    simp only [exec, execShift32] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | shift op d n =>
    simp only [exec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | xop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
  | vop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
  | vmovdquLoad len d m =>
    cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl
  | vmovdquStore len m r =>
    cases len
    · simp only [exec, State.store128] at h; split at h <;> cases h; rfl
    · simp only [exec, State.store256] at h; split at h <;> cases h; rfl
  | store m r => simp only [exec, State.store64] at h; split at h <;> cases h; rfl
  | store32 m r => simp only [exec, State.store32] at h; split at h <;> cases h; rfl
  | store8 m r => simp only [exec, State.store8] at h; split at h <;> cases h; rfl
  | movdquStore m r => simp only [exec, State.store128] at h; split at h <;> cases h; rfl
  | stmxcsr m => simp only [exec, State.store32] at h; split at h <;> cases h; rfl
  | mov | mov32 | movzx8 | movdquLoad | vbroadcasti128 =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | bswap32 | bswap | movImm64 | lfence =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl

theorem execBlock_mxcsr {is : List Instr} (hc : ∀ i ∈ is, loadsMxcsr i = false)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.mxcsr = s.mxcsr := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
      exec_mxcsr (hc i (List.mem_cons_self ..)) he]

/-- Code that never loads MXCSR keeps it. -/
theorem Exec.mxcsr {c : Prog isa} (hc : ∀ i ∈ instrs c, loadsMxcsr i = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.mxcsr = s.mxcsr := by
  induction h with
  | block h => exact execBlock_mxcsr hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ fun i hi => hc i (List.mem_append_right _ hi), ih₁ fun i hi => hc i (List.mem_append_left _ hi)]
  | iteT _ _ ih => exact ih fun i hi => hc i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hc i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | frame hp => simp only [isa, reduceCtorEq] at hp
  | call hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc

/-- The calling-convention obligations other than MXCSR's: the callee-saved
registers and the return address. -/
def gprPreserved (s s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
  s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64

theorem abiPreserved.gpr {s s' : State} (h : abiPreserved s s') : gprPreserved s s' := ⟨h.1, h.2.1⟩

/-- The calling-convention obligations of code that never loads MXCSR (the
kernel checks `hc` by evaluating the code), from the others. -/
theorem abiPreserved_of_exec {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true)
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : gprPreserved s s') :
    abiPreserved s s' := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  exact ⟨h.1, h.2, by rw [Exec.mxcsr (fun i hi => by simpa using hc i hi) he]⟩

end VG.X86_64
