import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# x86-64: the calling-convention obligations

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
  | vmovdqu32Store m r => simp only [exec, State.store512] at h; split at h <;> cases h; rfl
  | zop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
  | mov | mov32 | movzx8 | movdquLoad | vbroadcasti128 | vmovdqu32Load | vbroadcasti32x4 | zbcst =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | bswap32 | bswap | movImm64 | lfence | mul | andn32 | andn | vpmovmskb =>
    simp only [exec, Option.some.injEq] at h; subst h; rfl
  | rorx32 => simp only [exec, execRorx32] at h; split at h <;> cases h; rfl
  | rorx => simp only [exec, execRorx] at h; split at h <;> cases h; rfl
  | mulx =>
    simp only [exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | adcx =>
    simp only [exec, execAdcx] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | adox =>
    simp only [exec, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | push | pop => simp only [exec, reduceCtorEq] at h

theorem pushRegs_mxcsr (s : State) (rs : List Reg) : (pushRegs s rs).mxcsr = s.mxcsr := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem popReg_mxcsr (s : State) (r : Reg) (k : Nat) : (popReg s r k).mxcsr = s.mxcsr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

/-- A frame's push and pop keep MXCSR. -/
theorem push_mxcsr {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.mxcsr = s.mxcsr := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h
  exact pushRegs_mxcsr _ _

theorem pop_mxcsr {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mxcsr = s₂.mxcsr := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  exact popReg_mxcsr _ _ _

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
  | frame hp _ hq ih =>
    rw [pop_mxcsr hq, ih fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)),
      push_mxcsr hp]
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

/-- `WP.mono`, knowing that code that never loads MXCSR keeps it (the kernel
checks `hc` by evaluating the code). -/
theorem WP.mono_mx {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q R : State → Prop} (h : WP isa c s Q) (hq : ∀ s', Q s' → s'.mxcsr = s.mxcsr → R s') :
    WP isa c s R := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  obtain ⟨t, s', he, hQ⟩ := h
  exact ⟨t, s', he, hq s' hQ (Exec.mxcsr (fun i hi => by simpa using hc i hi) he)⟩

end VG.X86_64
