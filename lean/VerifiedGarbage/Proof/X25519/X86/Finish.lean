import VerifiedGarbage.Proof.X25519.X86.Setup
import VerifiedGarbage.Proof.X25519.X86.Invert

/-!
# X25519 on x86 (32-bit): the end of the ladder, and the result

The swap after the loop, and `finish`: `x2 · z2^(p-2)` (with `z2^(p-2)` in
`T1`), reduced fully, stored to `out`, and the saved registers restored.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The swap after the loop. -/
theorem lastSwap_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : LInv x k x1 s₀ 0 s) :
    WP isa (.block lastSwap) s fun s' => Base x k s₀ s' ∧
      F s'.mem x X2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).x2
        (ladderAfter k x1 0).x3).1 ∧
      F s'.mem x Z2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).z2
        (ladderAfter k x1 0).z3).1 := by
  have hfit := h.ctx.fit
  have hsw := ladderAfter_swap_le k x1 (n := 0) (by decide)
  simp only [lastSwap, List.cons_append, List.nil_append]
  refine Wp.wp_ldm h.ctx.edi (h.ctx.inRW (by decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_movi fun s₂ u₂ => Wp.wp_sub fun s₃ u₃ _ => ?_
  have k₃ : Keep s s₃ := (updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have b₃ : Base x k s₀ s₃ := h.toBase.ops k₃ (by rw [m₃]; exact Frame.refl _ _)
  have ecx₃ : s₃.gpr .ecx = mask (ladderAfter k x1 0).swap := by
    rw [u₃.gpr, u₂.gpr, u₂.other .edx (by decide), u₁.gpr]
    show 0 - wd s.mem x SWAP = _
    rw [h.swap]; rfl
  refine WP.block_append (WP.mono (cswap_ok b₃.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₃) fun s₄ ⟨k₄, ecx₄, f₄, x₄, _⟩ => ?_)
  have b₄ := b₃.ops k₄ (frame2_wide hfit f₄ (by decide) (by decide))
  refine WP.mono (cswap_ok b₄.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₄.trans ecx₃)) fun s₅ ⟨k₅, _, f₅, x₅, _⟩ => ⟨b₄.ops k₅ (frame2_wide hfit f₅ (by decide) (by decide)), ?_, ?_⟩
  · rw [F_frame2 hfit f₅ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ x₄, m₃, h.vx2, h.vx3,
      cswap_fst]
  · rw [F_ite _ x₅, F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide), m₃, h.vz2, h.vz3, cswap_fst]

theorem runI_X2 (V : Nat → Fe) : runI invSteps V X2 = V X2 := by
  simp only [runI, invSteps, IStep.run, X86.run, opOut, opVal, Function.update_apply, T0, T1, T2, T3, X2]
  simp (config := {decide := true}) only [ite_false]

/-- The inversion. -/
theorem invert_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (h : Base x k s₀ s) :
    WP isa Impl.X25519.X86.invert s fun s' => Base x k s₀ s' ∧
      F s'.mem x T1 = VG.Proof.X25519.invert (F s.mem x Z2) ∧ F s'.mem x X2 = F s.mem x X2 := by
  rw [invert_eq]
  exact WP.mono (progOf_ok invSteps h invSteps_valid) fun s' ⟨b, e⟩ =>
    ⟨b, by rw [e _ (by decide), runI_invert], by rw [e _ (by decide), runI_X2]⟩

/-! ## The result -/

theorem num_shift (f : Nat → Nat) (n : Nat) : num f (n + 1) = f 0 + 2 ^ 32 * num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

/-- The digits of a number of words. -/
theorem num_digit : ∀ (j : Nat) {f : Nat → Nat} {n : Nat}, (∀ k < n, f k < 2 ^ 32) → j < n →
    num f n / (2 ^ 32) ^ j % 2 ^ 32 = f j
  | 0, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 hj)]
  | j + 1, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_succ (2 ^ 32) j, Nat.mul_comm ((2 ^ 32) ^ j) (2 ^ 32), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (h 0 (by omega_using [])), Nat.zero_add]
    exact num_digit j (fun k hk => h (k + 1) (by omega_using [hk])) (by omega_using [hj])

/-- The words stored to `out` so far: those of `X2`. -/
structure OInv (s₀ sF : State) (n : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esi : s.gpr .esi = arg s₀ 0
  esp : s.gpr .esp = sF.gpr .esp
  rd : s.rd = sF.rd
  wr : s.wr = sF.wr
  frame : Frame [outR s₀] sF.mem s.mem
  words : ∀ j < n, wd s.mem (arg s₀ 0) (4 * j) = wd sF.mem (arg s₀ 3) (X2 + 4 * j)

theorem out_contains {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 8) :
    (outR s₀).Contains (addr (arg s₀ 0) (4 * j)) 4 := by
  have := sub_contains (x := arg s₀ 0) (a := 0) (k := 32) (d := 4 * j) (n := 4)
    (by have := hp.out_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hj]) (by decide)
  rwa [sub, addr_zero] at this

theorem outWord_ok {s₀ sF s : State} (hp : Pre s₀) (hsF : sF.wr = s₀.wr) {n : Nat} (hn : n < 8)
    (h : OInv s₀ sF n s) :
    WP isa (.block [.mov .eax (.mem (sc (X2 + 4 * n))), .store (at_ .esi (4 * n)) .eax]) s (OInv s₀ sF (n + 1)) := by
  have hfit := hp.sc_fit
  refine Wp.wp_ldm h.edi ⟨_, by rw [h.wr, hsF]; exact List.mem_append_right _ hp.sc_in,
    scR_contains hfit (by simp only [X2]; omega_using [hn]) (by decide)⟩ fun s₁ u₁ => ?_
  refine Wp.wp_stm (by rw [u₁.other _ (by decide), h.esi]) ⟨_, by rw [u₁.wr, h.wr, hsF]; exact hp.out_in,
    out_contains hp hn⟩ fun s₂ u₂ => WP.block_nil ?_
  have hsame : wd s.mem (arg s₀ 3) (X2 + 4 * n) = wd sF.mem (arg s₀ 3) (X2 + 4 * n) :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
      rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [X2]; omega_using [hn])
        (by simp only [X2]; omega_using [hn])
  refine ⟨by rw [u₂.gpr, u₁.other _ (by decide), h.edi], by rw [u₂.gpr, u₁.other _ (by decide), h.esi],
    by rw [u₂.gpr, u₁.other _ (by decide), h.esp], by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], ?_,
    fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains hp hn)
  · rw [u₂.mem, u₁.mem, u₁.gpr]
    have hof := hp.out_fit
    by_cases e : j = n
    · subst e; rw [wd_write_self]; exact hsame
    · rw [wd_write_ne _ _ (by omega_using [hof, hj, hn]) (by omega_using [hof, hn]) (by omega_using [hj, e])]
      exact h.words j (by omega_using [hj, e])

theorem outWords_ok {s₀ sF : State} (hp : Pre s₀) (hsF : sF.wr = s₀.wr) : ∀ n ≤ 8, ∀ s, OInv s₀ sF 0 s →
    WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (sc (X2 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s (OInv s₀ sF n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (outWords_ok hp hsF n (by omega_using [hn]) s h) fun s₁ h₁ =>
      outWord_ok hp hsF (by omega_using [hn]) h₁)

theorem restore_eq : restore =
    .mov .eax (.reg .edi) :: (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) := rfl

/-- The saved registers restored. -/
theorem restore_ok {x : BitVec 32} {s s₀ : State} (hc : Ctx 4096 x s) (hs : Spill.Saved s.mem (addr x) s₀.gpr savedSlots) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .esp = s.gpr .esp ∧ ∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r := by
  rw [restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  refine Spill.restore_ok _ (by decide)
    (fun p h => by
      rw [ea, u₁.rd, u₁.wr]; exact hc.inRW (by have := savedSlots_bound p (by revert p h; decide); omega_using [this])
        (by decide))
    (by rw [ea, u₁.mem]; exact hs.sub (by decide)) fun s' r' => WP.block_nil ⟨by rw [r'.mem, u₁.mem],
      by rw [r'.other _ (by decide), u₁.other _ (by decide)],
      fun r hr hsp => r'.regs r (by revert hsp; revert hr; revert r; decide)⟩

end VG.Proof.X25519.X86
