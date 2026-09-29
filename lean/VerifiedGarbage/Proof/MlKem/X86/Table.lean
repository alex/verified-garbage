import VerifiedGarbage.Proof.MlKem.X86.Unpack
import VerifiedGarbage.Impl.MlKem.X86.Ntt
import VerifiedGarbage.Proof.MlKem.Ntt

/-!
# ML-KEM on x86 (32-bit): writing a table of constants

Untrusted: everything here is checked by Lean. `table T b` stores the 128
entries of `T` as words at `[b]`, through `edx` (`table_spec`), one entry at
a time (`tableN`), so that each step is a short symbolic execution. The
table is read like the first half of a polynomial (`coeffAt`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- Entry `k` of the table. -/
def entry (T : List Nat) (b : Reg) (k : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ b (4 * k)) .edx]

/-- The first `n` entries. -/
def tableN (T : List Nat) (b : Reg) (n : Nat) : List Instr := (List.range n).flatMap (entry T b)

theorem table_eq (T : List Nat) (b : Reg) : table T b = tableN T b 128 := rfl

theorem tableN_succ (T : List Nat) (b : Reg) (n : Nat) :
    tableN T b (n + 1) = tableN T b n ++ entry T b n := by
  simp only [tableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` entries of `T` at `p`, from `b` at `p`: only `edx`, the flags and the words at `p`
change. -/
theorem tableN_spec (T : List Nat) {b : Reg} (hb : b ≠ .edx) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 128 →
      (∀ k < 128, s.ea (at_ b (4 * k)) = coeffAddr p k) → (∀ k < 128, InRegions s.wr (coeffAddr p k) 4) →
      (∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, coeffAt s'.mem p k = BitVec.ofNat 32 (T.getD k 0)) →
        (∀ k, n ≤ k → k < 256 → coeffAt s'.mem p k = coeffAt s.mem p k) → WP isa (.block is) s' P) →
      WP isa (.block (tableN T b n ++ is)) s P
  | 0, is, s, P, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega))
      fun _ _ _ => rfl
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [tableN_succ, List.append_assoc]
    refine tableN_spec T hb n _ s P (by omega) hea hin fun s₁ o₁ f₁ c₁ d₁ => ?_
    have ea₁ : s₁.ea (at_ b (4 * n)) = coeffAddr p n := by
      rw [← hea n (by omega)]; simp only [State.ea, at_, o₁.gpr b (by simp [hb])]
    have hn' : n < Spec.MlKem.n := by rw [n_eq]; omega
    refine wp_cons (s' := s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0)))
      (by simp only [exec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0))).wr
        ((s₁.setReg .edx (BitVec.ofNat 32 (T.getD n 0))).ea (at_ b (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, hb, ite_false]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁, o₁.wr]
      exact hin n (by omega)
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr⟩ ?_ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, hb, ite_false]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn')
    · intro j hj
      simp only [State.ea, at_, State.setReg, hb, ite_false, ite_true]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlKem.n by rw [n_eq]; omega) hn']
      by_cases e : n = j
      · rw [ite_eq_left e, e]
      · rw [ite_eq_right e]; exact c₁ j (by omega)
    · intro j hj hj'
      simp only [State.ea, at_, State.setReg, hb, ite_false, ite_true]
      rw [show (s₁.gpr b + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlKem.n by rw [n_eq]; omega) hn', ite_eq_right (by omega),
        d₁ j (by omega) hj']

theorem table_spec (T : List Nat) {b : Reg} (hb : b ≠ .edx) {p : Addr} (is : List Instr) (s : State)
    (P : State → Prop) (hea : ∀ k < 128, s.ea (at_ b (4 * k)) = coeffAddr p k)
    (hin : ∀ k < 128, InRegions s.wr (coeffAddr p k) 4)
    (k : ∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
      (∀ k < 128, coeffAt s'.mem p k = BitVec.ofNat 32 (T.getD k 0)) → WP isa (.block is) s' P) :
    WP isa (.block (table T b ++ is)) s P := by
  rw [table_eq]
  exact tableN_spec T hb 128 is s P (Nat.le_refl _) hea hin fun s' o f c _ => k s' o f c

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

end VG.Proof.MlKem.X86
