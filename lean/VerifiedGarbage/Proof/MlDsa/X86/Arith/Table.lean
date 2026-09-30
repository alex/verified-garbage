import VerifiedGarbage.Proof.MlDsa.X86.Arith.Bfly

/-!
# ML-DSA on x86 (32-bit): writing a table of constants

Untrusted: everything here is checked by Lean. `table t` stores the 256
entries of `t` as words at `[eax]`, through `edx` (`table_spec`), one entry
at a time (`tableN`), so that each step is a short symbolic execution. The
table is read like a polynomial (`coeffAt`).
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n coeffAt)
open VG.Proof.MlKem.X86 (wp_cons wp_store)

/-- `s'` is `s` but for the registers `ds`, the flags and memory. -/
structure Regs (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- Entry `k` of the table. -/
def entry (T : List Nat) (k : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ .eax (4 * k)) .edx]

/-- The first `n` entries. -/
def tableN (T : List Nat) (n : Nat) : List Instr := (List.range n).flatMap (entry T)

theorem table_eq (T : List Nat) : table T = tableN T 256 := rfl

theorem tableN_succ (t : List Nat) (n : Nat) : tableN t (n + 1) = tableN t n ++ entry t n := by
  simp only [tableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` entries of `t` at `p`, from `eax` at `p`: only `edx`, the
flags and the words at `p` change. -/
theorem tableN_spec (t : List Nat) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 256 →
      (∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k) → (∀ k < 256, InRegions s.wr (coeffAddr p k) 4) →
      (∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) →
      WP isa (.block (tableN t n ++ is)) s P
  | 0, is, s, P, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega))
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [tableN_succ, List.append_assoc]
    refine tableN_spec t n _ s P (by omega) hea hin fun s₁ o₁ f₁ c₁ => ?_
    have ea₁ : s₁.ea (at_ .eax (4 * n)) = coeffAddr p n := by
      rw [← hea n (by omega)]; simp only [State.ea, at_, o₁.gpr .eax (by decide)]
    have hn' : n < Spec.MlDsa.n := by rw [n_eq]; omega
    refine wp_cons (s' := s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0)))
      (by simp only [exec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).wr
        ((s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).ea (at_ .eax (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁, o₁.wr]
      exact hin n (by omega)
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr⟩ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn')
    · intro j hj
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false, ite_true]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlDsa.n by rw [n_eq]; omega) hn']
      by_cases e : n = j
      · rw [ite_eq_left e, e]
      · rw [ite_eq_right e]; exact c₁ j (by omega)

theorem table_spec (t : List Nat) {p : Addr} (is : List Instr) (s : State) (P : State → Prop)
    (hea : ∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k)
    (hin : ∀ k < 256, InRegions s.wr (coeffAddr p k) 4)
    (k : ∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
      (∀ k < 256, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) :
    WP isa (.block (table t ++ is)) s P := by
  rw [table_eq]
  exact tableN_spec t 256 is s P (Nat.le_refl _) hea hin k

theorem montZeta_eq {k : Nat} (hk : k < 256) :
    montZetaTable.getD k 0 = (Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← zetaNat_eq]
  exact (by decide +kernel : ∀ k < 256, montZetaTable.getD k 0 = zetaNat k * 2 ^ 32 % 8380417) k hk

theorem montNegZeta_eq {k : Nat} (hk : k < 256) :
    montNegZetaTable.getD k 0 = (-Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← negZetaNat_eq]
  exact (by decide +kernel : ∀ k < 256, montNegZetaTable.getD k 0 = negZetaNat k * 2 ^ 32 % 8380417) k hk

end VG.Proof.MlDsa.X86.Arith
