import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Impl.Weierstrass.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on x86-64: copies, selections and constants

`copy n o a` writes `[a]` to `[o]` (`copy_ok`), `sel n o a b` writes `[a]` or
`[b]` to `[o]` by the mask `rcx` (`sel_ok`; `o` may be `a` or `b`), `selPt`
does so for the three coordinates of a point (`selPt_ok`), and `setConst n o x`
writes `x` (`setConst_ok`). Each changes only `[o]` and `rax` (and `rdx` for
the selections), and keeps the regions.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → o + 8 * n ≤ size → a + 8 * n ≤ size → (o ≤ a ∨ a + 8 * n ≤ o) →
    WP isa (.block (copy n o a)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base a n ∧ KeepRegs [.rax] s s' ∧
      Outside base o (8 * n) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | n + 1, s, base, o, a, hs, ho, ha, hsep => by
    have hn := hs.nowrap
    rw [copy, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rax (.mem (sc a)), .store (sc o) .rax]) s
        (fun s₁ => s₁.mem = s.mem.writeW (off base o) (word s.mem base a) ∧ KeepRegs [.rax] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.mem_setReg, reduceCtorEq, ite_true, ite_false, hs.rdi, ld_sc hs (d := a) (by omega),
        st_sc hs (d := o) (by omega), Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    have e₁ : wordsVal s₁.mem base (a + 8) n = wordsVal s.mem base (a + 8) n :=
      O₁.wordsVal (by omega) (by omega)
    refine WP.mono (copy_ok n hs₁ (o := o + 8) (a := a + 8) (by omega) (by omega) (by omega))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    rw [wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, e₂, e₁, wordsVal]

/-- The word a selection stores. -/
theorem sel_word (c : Bool) (x y : BitVec 64) :
    x ^^^ ((y ^^^ x) &&& (if c then BitVec.allOnes 64 else 0)) = if c then y else x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have z : ∀ {w} j, (0 : BitVec w).getLsbD j = false := fun _ => BitVec.getLsbD_zero
  cases c <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_xor, BitVec.getLsbD_and,
      BitVec.getLsbD_allOnes, z, hi, decide_true, hx, hy, Bool.and_false, Bool.and_true, Bool.xor_false,
      Bool.xor_true, Bool.not_false, Bool.not_true]

/-- `[o] = [b]` if the mask `rcx` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok {size : Nat} (c : Bool) : ∀ (n : Nat) {s : State} {base : Addr} {o a b : Nat},
    Scr s base size → s.gpr .rcx = (if c then BitVec.allOnes 64 else 0) →
    o + 8 * n ≤ size → a + 8 * n ≤ size → b + 8 * n ≤ size →
    (o ≤ a ∨ a + 8 * n ≤ o) → (o ≤ b ∨ b + 8 * n ≤ o) →
    WP isa (.block (sel n o a b)) s fun s' =>
      wordsVal s'.mem base o n = (if c then wordsVal s.mem base b n else wordsVal s.mem base a n) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base o (8 * n) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl,
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | n + 1, s, base, o, a, b, hs, hc, ho, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [sel, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rax (.mem (sc a)), .mov .rdx (.mem (sc b)),
        .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
        .store (sc o) .rax]) s (fun s₁ => s₁.mem = s.mem.writeW (off base o)
          (if c then word s.mem base b else word s.mem base a) ∧ KeepRegs [.rax, .rdx] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs.rdi, hc, ld_sc hs (d := a) (by omega), ld_sc hs (d := b) (by omega),
        st_sc hs (d := o) (by omega), Option.some.injEq, exists_eq_left', sel_word]
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]) fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    have ea : wordsVal s₁.mem base (a + 8) n = wordsVal s.mem base (a + 8) n :=
      O₁.wordsVal (by omega) (by omega)
    have eb : wordsVal s₁.mem base (b + 8) n = wordsVal s.mem base (b + 8) n :=
      O₁.wordsVal (by omega) (by omega)
    refine WP.mono (sel_ok c n hs₁ (o := o + 8) (a := a + 8) (b := b + 8)
      (by rw [k₁.gpr _ (by decide), hc]) (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    rw [wordsVal, O₂.word (by omega) (by omega), m₁, word_writeW_self, e₂, ea, eb]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, wordsVal]

/-- `o = b` if the mask `rcx` is all ones (`c`), `a` if it is zero, for points
whose slots are in the working space, with `o`'s apart from each other and
from `a`'s and `b`'s. -/
theorem selPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o a b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      KeepRegs [.rax, .rdx] s s' ∧
      ∀ x, (ofs base x < o.x ∨ o.x + 8 * n ≤ ofs base x) → (ofs base x < o.y ∨ o.y + 8 * n ≤ ofs base x) →
        (ofs base x < o.z ∨ o.z + 8 * n ≤ ofs base x) → s'.mem x = s.mem x := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs hc iox iax ibx (by omega_using [xax]) (by omega_using [xbx]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n hs₁ (by rw [k₁.gpr _ (by decide), hc]) ioy iay iby (by omega_using [yay])
    (by omega_using [yby])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (sel_ok c n hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz iaz ibz
    (by omega_using [zaz]) (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x h₁ h₂ h₃ => by rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]

/-! ## Constants -/

/-- One word of `setConst`. -/
def constStep (o x j : Nat) : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 (x >>> (64 * j))), .store (sc (o + 8 * j)) .rax]

theorem setConst_eq (n o x : Nat) : setConst n o x = (List.range n).flatMap (constStep o x) := rfl

theorem constSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x : Nat} :
    ∀ k, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (constStep o x))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = BitVec.ofNat 64 (x >>> (64 * j))) ∧
      KeepRegs [.rax] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (constSteps_ok hs k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (show WP isa (.block (constStep o x k)) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (o + 8 * k)) (BitVec.ofNat 64 (x >>> (64 * k))) ∧
          KeepRegs [.rax] s₁ s₂) by
      apply WP.of_runBlock
      simp only [constStep, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_sc,
        RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_true, ite_false,
        hs₁.rdi, st_sc hs₁ (d := o + 8 * k) (by omega), Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]

/-- `[o] = x`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o x : Nat}
    (ho : o + 8 * n ≤ size) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun s' =>
      wordsVal s'.mem base o n = x ∧ KeepRegs [.rax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [setConst_eq]
  exact WP.mono (constSteps_ok hs n ho) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_of_shifts _ _ o n x hx e, k, O⟩

end VG.Proof.Weierstrass.X86_64
