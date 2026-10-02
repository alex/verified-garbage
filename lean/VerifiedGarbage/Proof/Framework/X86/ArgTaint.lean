import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# A taint state for code reading its stack arguments (x86, 32-bit)

Pieces of code between calls (proved by relating two runs, `RelCT`) may read
their function's stack arguments again: `argTaint rs n` makes `esp`, the
registers `rs` and the `n - 4` bytes of arguments public, which two runs
agree on as long as the arguments are the same and lie outside the writable
regions (`agree_argTaint`).
-/

namespace VG.X86

/-- The taint in which `esp`, the registers `rs` and the `n - 4` bytes of
stack arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := false, argLen := n }

/-- The `k` words of arguments lie outside the writable regions, and do not wrap around. -/
def ArgsOut (k : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + (4 + 4 * k) ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4 + 4 * k⟩ r

theorem agree_argTaint {rs : List Reg} {k : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.gpr .esp = s₂.gpr .esp) (hw₁ : ArgsOut k s₁) (hw₂ : ArgsOut k s₂)
    (hm : ∀ i < k, arg s₁ i = arg s₂ i) : VG.X86.Taint.Agree (argTaint rs (4 + 4 * k)) s₁ s₂ := by
  have wf : ∀ s : State, ArgsOut k s → VG.X86.Taint.Wf (argTaint rs (4 + 4 * k)) s := fun s hs =>
    VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs.1, hs.2⟩, fun _ h => (List.not_mem_nil h).elim⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf s₁ hw₁, wf s₂ hw₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun j h4 hj => ?_⟩
  · simp only [argTaint, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hsp
    · exact h r hr
  · simp only [argTaint] at hj
    rw [show VG.X86.Taint.depth (argTaint rs (4 + 4 * k)).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hw₁.1 h4 hj, VG.X86.Taint.argByte_eq hw₂.1 h4 hj,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (hm _ (by omega))

end VG.X86
