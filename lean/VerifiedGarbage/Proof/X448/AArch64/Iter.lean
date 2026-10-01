import VerifiedGarbage.Proof.X448.AArch64.BitStep
import VerifiedGarbage.Proof.X448.AArch64.Counters

/-!
# X448 on AArch64: the Montgomery ladder

Untrusted: everything here is checked by Lean. Each iteration consumes one
scalar bit and updates the five field slots according to `ladderStep`.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def stepEnv (sw : Bool) (e : Env) : Env :=
  applyOps stepFields (opSwap 2 4 sw (opSwap 1 3 sw e))

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem stepEnv_eval (e : Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 0 = u ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [ladderStep_eq]
  simp (config := {decide := true}) only [stepEnv, applyOps, stepFields, FieldOp.apply,
    opMul, opAdd, opSub, opA24, opSwap, Function.update_apply,
    cswap_fst, cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem swaps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (cswap X2 X3 ++ cswap Z2 Z3)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSwap 2 4 sw (opSwap 1 3 sw (E s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs hb 1 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  refine WP.mono (cswapE (tk.scr hs) tb 2 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, _, ue⟩ =>
    ⟨tk.trans uk, ub, by rw [ue, te]⟩

theorem counter_zero {s : State} {n : Nat} (hn : n < 2 ^ 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 n) : (s.gpr .x19 == 0) = decide (n = 0) := by
  rw [hc]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rfl
  · rw [decide_eq_false (by omega)]
    apply beq_false_of_ne
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by simp; omega)

/-- The complete loop invariant, including its memory frame. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.x19 :: workRegs) s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  mem : Outside2 base 16 2864 ACC 512 s₀.mem s.mem
  x1 : E s.mem base 0 = u
  x2 : E s.mem base 1 = (ladderAfter k u n).x2
  z2 : E s.mem base 2 = (ladderAfter k u n).z2
  x3 : E s.mem base 3 = (ladderAfter k u n).x3
  z3 : E s.mem base 4 = (ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : LInv base k u s₀ s (n + 1)) :
    WP isa step s fun t => LInv base k u s₀ t n ∧ (t.gpr .x19 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [step, WP.seq_iff,
    show stepHead = stepPre ++ (cswap X2 X3 ++ cswap Z2 Z3) by
      simp only [stepHead, stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (stepPre_ok hs hn hi.x19 (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr, hs.nowrap⟩
  have out₁ : Outside base SWAP 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : Index, ∀ j < 16, limbs s₁.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (slot_bound i) (by decide)) hj
  have e₁ : E s₁.mem base = E s.mem base := by
    funext i; exact congrArg toFe (valN_congr (l₁ i))
  have bb₁ : BoundedEnv s₁.mem base := by
    intro i j hj; rw [l₁ i j hj]; exact hi.bounded i j hj
  refine WP.mono (swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_
  rw [← stepFields_impl]
  refine WP.mono (ops_ok (k₂.scr hs₁) bb₂ stepFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃ : s₃.gpr .x19 = BitVec.ofNat 64 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := stepEnv_eval (E s.mem base) (ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : E s₃.mem base = stepEnv (decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1))
      (E s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, bb₃, ?_, b₃, ?_, vals.1, vals.2.1, vals.2.2.1,
    vals.2.2.2.1, vals.2.2.2.2, ?_⟩, counter_zero (by omega) b₃⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ workRegs := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.x19, .x4, .x5, .x6, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, ladderAfter_step k u hn]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.X448.AArch64
