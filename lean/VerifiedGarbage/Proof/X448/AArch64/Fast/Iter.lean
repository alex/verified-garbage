import VerifiedGarbage.Proof.X448.AArch64.Fast.Phases
import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter

/-!
# X448 on AArch64: the Montgomery ladder's iterations

Untrusted: everything here is checked by Lean. Each iteration consumes one
scalar bit and updates the five ladder slots according to `ladderStep`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask writeW_outside)
open VG.Proof.X448.AArch64.Weak (Index Env cswap_fst cswap_snd counter_zero ofs_off')
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (ladderAfter ladderStep_eq ladderAfter_step bit bit_le ladderAfter_swap_le)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def stepEnvF (sw : Bool) (e : Env) : Env := stepOpsEnv (bflyEnv sw e)

theorem stepEnvF_eval (e : Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    stepEnvF (decide (st.swap ^^^ bit k t = 1)) e 0 = u ∧
    stepEnvF (decide (st.swap ^^^ bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    stepEnvF (decide (st.swap ^^^ bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    stepEnvF (decide (st.swap ^^^ bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    stepEnvF (decide (st.swap ^^^ bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [ladderStep_eq]
  cases hsw : decide (st.swap ^^^ bit k t = 1)
  all_goals
    simp (config := {decide := true}) only [stepEnvF, stepOpsEnv, bflyEnv, swp, Function.update_apply,
      cswap_fst, cswap_snd, hsw, h0, h1, h2, h3, h4, ite_true, ite_false, Bool.false_eq_true]

/-- The ladder's loop invariant. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  red : ∀ i : Index, i.val ∈ [0, 1, 2, 3, 4] → Bnd Mb s.mem base (slot i.val)
  regs : Keeps (.x19 :: fclob) s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  mem : Outside2 base 16 2864 ACC 1152 s₀.mem s.mem
  x1 : EV s.mem base 0 = u
  x2 : EV s.mem base 1 = (ladderAfter k u n).x2
  z2 : EV s.mem base 2 = (ladderAfter k u n).z2
  x3 : EV s.mem base 3 = (ladderAfter k u n).x3
  z3 : EV s.mem base 4 = (ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : LInv base k u s₀ s (n + 1)) :
    WP isa Impl.X448.AArch64.Fast.step s fun t => LInv base k u s₀ t n ∧ (t.gpr .x19 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [Impl.X448.AArch64.Fast.step, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.stepPre_ok hs hn hi.x19 (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr,
    hs.nowrap⟩
  have out₁ : Outside base SWAP 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : Index, ∀ j < 8, limbs s₁.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.AArch64.Weak.slot_bound i) (by decide)) (by omega)
  have same₁ : Same base [] s.mem s₁.mem := fun i _ j hj => l₁ i j hj
  have e₁ : EV s₁.mem base = EV s.mem base := funext fun i => same₁.env (by simp)
  refine WP.mono (bflyE hs₁ (fun i => same₁.bnd (by simp) (hi.env i))
    (fun i hi' => same₁.bnd (by simp) (hi.red i (by simp at hi' ⊢; omega))) c₁) fun s₂ ⟨k₂, b₂, sm₂, e₂⟩ => ?_
  have hs₂ := k₂.scr hs₁
  have r₂ : Bnd Mb s₂.mem base (slot (0 : Index).val) :=
    sm₂.bnd (by decide) (same₁.bnd (by simp) (hi.red 0 (by decide)))
  refine WP.mono (stepOps_ok hs₂ b₂ r₂) fun s₃ ⟨k₃, b₃, r₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃' : s₃.gpr .x19 = BitVec.ofNat 64 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := stepEnvF_eval (EV s.mem base) (ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : EV s₃.mem base = stepEnvF (decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1))
      (EV s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, b₃, r₃, ?_, b₃', ?_, vals.1, vals.2.1, vals.2.2.1, vals.2.2.2.1, vals.2.2.2.2, ?_⟩,
    counter_zero (by omega) b₃'⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ fclob := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.x19, .x4, .x5, .x6, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (by subst r; decide), fun h => hwork (by subst r; decide),
        fun h => hwork (by subst r; decide), fun h => hwork (by subst r; decide),
        fun h => hwork (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, ladderAfter_step k u hn]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.X448.AArch64.Fast
