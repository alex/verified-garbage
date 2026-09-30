import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call

/-!
# ML-DSA signing on ARMv7: blocks that leak only their pointers

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/MlDsa/X86_64/Sign/BlockTr.lean`): a block whose memory accesses are
`[b, #off]` with `b` among registers `rs` that it never writes leaks the
same from two states that agree on `rs` (`block_tr`). Unlike the taint
analysis, which evaluates the code, this holds for code with immediates and
offsets that are variables, such as the pieces of the function indexed by a
polynomial or an entry of `Â`; `blockOk` is checked by `decide`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm

/-- The registers the address an instruction accesses uses: its base for the
loads and stores of `[b, #off]`, none for the instructions without a memory
access, and `none` for the others (the stack pointer's). -/
def memBase : Instr → Option (List Reg)
  | .ldr _ n _ | .str _ n _ | .ldrb _ n _ | .strb _ n _ => some [n]
  | .ldrSp .. | .push _ | .pop .. => none
  | _ => some []

/-- Every instruction's addresses use only `rs`, which none writes. -/
def blockOk (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (match memBase i with | some l => l.all (rs.contains ·) | none => false) &&
    rs.all fun r => dstOf i != some r

theorem addrs_agree {rs : List Reg} {i : Instr} {l : List Reg} (h : memBase i = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : addrs i s = addrs i s' := by
  cases i <;> simp only [memBase, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    first | rfl | simp only [addrs, hs _ (hl _ (List.mem_singleton_self _))]

theorem blockOk_cons {rs : List Reg} {i : Instr} {is : List Instr} (h : blockOk rs (i :: is) = true) :
    (∃ l, memBase i = some l ∧ ∀ r ∈ l, r ∈ rs) ∧ (∀ r ∈ rs, dstOf i ≠ some r) ∧ blockOk rs is = true := by
  simp only [blockOk, List.all_cons, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hm, hc⟩, hr⟩ := h
  refine ⟨?_, hc, by simpa [blockOk] using hr⟩
  revert hm
  cases memBase i with
  | some l => intro hm; simp only [List.all_eq_true, List.contains_iff_mem] at hm; exact ⟨l, rfl, hm⟩
  | none => intro hm; cases hm

theorem execBlock_tr {rs : List Reg} : ∀ {is : List Instr}, blockOk rs is = true →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, hs, e₁, e₂ => by
    obtain ⟨⟨l, hl, hin⟩, hc, hrest⟩ := blockOk_cons h
    simp only [execBlock] at e₁ e₂
    split at e₁
    · cases e₁
    · rename_i a₁ ha₁
      split at e₂
      · cases e₂
      · rename_i a₂ ha₂
        obtain ⟨⟨u₁, v₁⟩, f₁, g₁⟩ := Option.map_eq_some_iff.mp e₁
        obtain ⟨⟨u₂, v₂⟩, f₂, g₂⟩ := Option.map_eq_some_iff.mp e₂
        simp only [Prod.mk.injEq] at g₁ g₂
        rw [← g₁.2, ← g₂.2, addrs_agree hl hin hs,
          execBlock_tr hrest (fun r hr => by rw [exec_gpr (hc r hr) ha₁, exec_gpr (hc r hr) ha₂, hs r hr]) f₁ f₂]

/-- A block that leaks only addresses from the registers `rs`, which it never writes. -/
theorem block_tr {rs : List Reg} {is : List Instr} (h : blockOk rs is = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_tr h (hP _ _ hp) e₁ e₂, trivial⟩

end VG.Proof.MlDsa.Arm.Sign
