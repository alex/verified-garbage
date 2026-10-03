import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds

/-!
# The four columns of a product

Untrusted: everything here is checked by Lean. For any registers and steps
whose accumulators `L` and `H` hold coefficients `d` and `d + 4` of `r` after
column `d` (`hsem`), the columns stage the limbs of both carry chains and
leave their last carries in `CL` and `CH`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)

/-- The registers a column may write. -/
def colWrites (R : Regs) (accs : List Acc) : List Reg := writes R accs ++ [CL, CH]

/-- What the columns guarantee after `n` of them. -/
structure ColInv (base : Addr) (o : Nat) (r : Nat → Nat) (s t : State) (n : Nat) : Prop where
  scr : Scr t base
  mask : t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)
  zero : t.gpr ZERO = 0
  out : Outside base o 64 s.mem t.mem
  lo : ∀ k < n, (word t.mem base (o + 8 * k)).toNat = chainLimb r 0 k
  hi : ∀ k < n, (word t.mem base (o + 8 * (4 + k))).toNat = chainLimb r 4 k
  cl : 0 < n → (t.gpr CL).toNat = chain r 0 n
  ch : 0 < n → (t.gpr CH).toNat = chain r 4 n

theorem colEnd_ok {s : State} {base : Addr} (hs : Scr s base) (t : Reg) (a : Acc) (c : Reg)
    (first : Bool) {o k : Nat} (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192) (hk : k < 8) (h₁ : t ≠ a.lo) (h₂ : t ≠ a.hi) (h₃ : t ≠ .x3)
    (h₄ : a.lo ≠ a.hi) (h₅ : a.lo ≠ ZERO) (h₆ : MASK ∉ [a.lo, a.hi]) (h₇ : a.lo ≠ .x3)
    (h₈ : a.hi ≠ .x3) (h₉ : a.lo ≠ .x12) (h₁₀ : a.hi ≠ .x12)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hz : s.gpr ZERO = 0)
    {V cin : Nat} (hV : accVal s a = V) (hc : first = false → (s.gpr c).toNat = cin)
    (h0 : first = true → cin = 0) (hlt : V + cin < 2 ^ 120) :
    WP isa (.block (colEnd t a c first o k)) s fun u =>
      u.mem = s.mem.writeW (off base (o + 8 * k)) (BitVec.ofNat 64 ((V + cin) % radix)) ∧
      (u.gpr c).toNat = (V + cin) / radix ∧ Keeps [a.lo, a.hi, t, c] s u := by
  cases first
  · simp only [colEnd, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    rw [show (Instr.adds .x a.lo a.lo c :: Instr.adc .x a.hi a.hi ZERO ::
        [Instr.logic .and .x t a.lo MASK, st t (o + 8 * k), .extr .x c a.hi a.lo 56]) =
        [Instr.adds .x a.lo a.lo c, .adc .x a.hi a.hi ZERO] ++
        [Instr.logic .and .x t a.lo MASK, st t (o + 8 * k), .extr .x c a.hi a.lo 56] from rfl,
      WP.block_append_iff]
    have hc' := hc rfl
    refine WP.mono (carryIn_ok s a c h₄ h₅ hz (by rw [hV, hc']; omega)) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := hs.of_keeps uk (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨Ne.symm h₇, Ne.symm h₈⟩, ⟨Ne.symm h₉, Ne.symm h₁₀⟩⟩)
    have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ h₆, hm]
    refine WP.mono (stage_ok us t a c (by omega) (by omega) h₁ h₂ h₃ um' (by rw [uv, hV, hc']; omega))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, uv, um, hV, hc']
    · rw [wc, uv, hV, hc']
    · refine (uk.mono ?_).trans (wk.mono ?_) <;> intro r hr <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
        rcases hr with h | h <;> simp [h]
  · simp only [colEnd, ite_true, List.nil_append]
    have hc' := h0 rfl
    subst hc'
    refine WP.mono (stage_ok hs t a c (by omega) (by omega) h₁ h₂ h₃ hm (by rw [hV]; omega))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, hV, Nat.add_zero]
    · rw [wc, hV, Nat.add_zero]
    · refine wk.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h]

/-- The carry and constant registers are not written by the steps, by `decide`. -/
abbrev ColRegs (R : Regs) (accs : List Acc) : Prop :=
  MASK ∉ colWrites R accs ∧ ZERO ∉ colWrites R accs ∧ CL ∉ writes R accs ∧ CH ∉ writes R accs ∧
  CL ≠ CH ∧ Reg.x3 ∉ [CL, CH] ∧ Reg.x12 ∉ [CL, CH]

theorem word_stage {m : Mem} {base : Addr} {o k j : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (hj : j < 8) (v : BitVec 64) :
    word (m.writeW (off base (o + 8 * k)) v) base (o + 8 * j) =
      if j = k then v else word m base (o + 8 * j) := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW m base (by omega) (by omega) (by omega)]
  by_cases h : j = k
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

theorem stage_outside (m : Mem) (base : Addr) {o k : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (v : BitVec 64) : Outside base o 64 m (m.writeW (off base (o + 8 * k)) v) := by
  exact (writeW_outside m base v (by omega)).mono (by omega) (by omega)

section
variable {R : Regs} {accs : List Acc} {L H : Acc} {col : Nat → List MOp} {b o : Nat}
  {r : Nat → Nat} {base : Addr}

theorem column_ok (hG : Good R accs) (hC : ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192)
    (hfit : Fits r) {d : Nat} (hd : d < 4) (hops : (col d).all (opOk (writes R accs) accs) = true)
    {t : State} {s : State} (hi : ColInv base o r s t d)
    (hsem : ∀ e, sem (srcVal t base b) e (col d) L = r d ∧ sem (srcVal t base b) e (col d) H = r (d + 4)) :
    WP isa (.block ((col d).flatMap (MOp.code R b) ++ colEnd R.t L CL (d == 0) o d ++
        colEnd R.t H CH (d == 0) o (d + 4))) t fun w =>
      ColInv base o r s w (d + 1) ∧ Keeps (colWrites R accs) t w ∧ Outside base o 64 t.mem w.mem := by
  obtain ⟨hM, hZ, hCL, hCH, hCC, h3, h12⟩ := hC
  have nM : MASK ∉ writes R accs := fun h => hM (List.mem_append_left _ h)
  have nZ : ZERO ∉ writes R accs := fun h => hZ (List.mem_append_left _ h)
  obtain ⟨Llh, Llo, Lhi⟩ := hG.acc hL
  obtain ⟨Hlh, Hlo, Hhi⟩ := hG.acc hH
  have x3w : Reg.x3 ∉ writes R accs := hG.2.2.2.2.2.1
  have x12w : Reg.x12 ∉ writes R accs := hG.2.2.2.2.2.2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (mops_ok hG hb8 hb (col d) hops hi.scr (v := srcVal t base b) (fun _ _ => rfl)
    (e := fun a => (accVal t a : Int)) (fun a _ => self_emod (pair_lt _ _))) fun u ⟨uv, um, uk⟩ => ?_
  have us : Scr u base := hG.scr hi.scr uk (fun _ h => h)
  obtain ⟨sL, sH⟩ := hsem (fun a => (accVal t a : Int))
  have rL : accVal u L = r d := exact_of_emod (uv L hL) sL (by
    have := hfit.low d hd; simp only [M]; omega)
  have rH : accVal u H = r (4 + d) := exact_of_emod (uv H hH) (by rw [sH, Nat.add_comm]) (by
    have := hfit.high d hd; simp only [M]; omega)
  have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ nM, hi.mask]
  have uz : u.gpr ZERO = 0 := by rw [uk.1 _ nZ, hi.zero]
  have tne : ∀ a ∈ accs, R.t ≠ a.lo ∧ R.t ≠ a.hi := fun a ha => by
    obtain ⟨-, h1, h2⟩ := hG.acc ha
    exact ⟨fun e => h1 (by simp [e]), fun e => h2 (by simp [e])⟩
  have t3 : R.t ≠ .x3 := fun e => x3w (e ▸ t_mem)
  have nmem : ∀ {q : Reg} {a : Acc}, a ∈ accs → q ∉ writes R accs → q ∉ [a.lo, a.hi] := by
    intro q a ha hq hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · exact hq (h ▸ lo_mem ha)
    · exact hq (h ▸ hi_mem ha)
  rw [WP.block_append_iff]
  have hcL : (d == 0) = false → (u.gpr CL).toNat = chain r 0 d := fun h => by
    rw [uk.1 _ hCL]; exact hi.cl (by simp at h; omega)
  have h0L : (d == 0) = true → chain r 0 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (colEnd_ok us R.t L CL (d == 0) (k := d) ho8 ho (by omega) (tne L hL).1 (tne L hL).2 t3 Llh
    (fun e => nZ (e ▸ lo_mem hL)) (nmem hL nM) (fun e => x3w (e ▸ lo_mem hL))
    (fun e => x3w (e ▸ hi_mem hL)) (fun e => x12w (e ▸ lo_mem hL)) (fun e => x12w (e ▸ hi_mem hL))
    um' uz rL hcL h0L (hfit.low d hd)) fun w ⟨wm, wc, wk⟩ => ?_
  have lnot : ∀ {q : Reg}, q ∉ writes R accs → q ≠ CL → q ∉ [L.lo, L.hi, R.t, CL] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ lo_mem hL)
    · exact hq (h ▸ hi_mem hL)
    · exact hq (h ▸ t_mem)
    · exact hc h
  have ws : Scr w base := us.of_keeps wk (by
    refine ⟨lnot x3w (fun e => h3 (by simp [e])), lnot x12w (fun e => h12 (by simp [e]))⟩)
  have wM : w.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by
    rw [wk.1 _ (lnot nM (fun e => hM (by simp [colWrites, e]))), um']
  have wZ : w.gpr ZERO = 0 := by
    rw [wk.1 _ (lnot nZ (fun e => hZ (by simp [colWrites, e]))), uz]
  have wH : accVal w H = r (4 + d) := by
    obtain ⟨d1, d2⟩ := hG.disj hH hL (Ne.symm hLH)
    rw [accVal_keep wk (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d1 (by simp [e])
        · exact d1 (by simp [e])
        · exact (tne H hH).1 e.symm
        · exact hCL (e ▸ lo_mem hH))
      (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d2 (by simp [e])
        · exact d2 (by simp [e])
        · exact (tne H hH).2 e.symm
        · exact hCL (e ▸ hi_mem hH)), rH]
  have hcH : (d == 0) = false → (w.gpr CH).toNat = chain r 4 d := fun h => by
    rw [wk.1 _ (lnot hCH (Ne.symm hCC)), uk.1 _ hCH]; exact hi.ch (by simp at h; omega)
  have h0H : (d == 0) = true → chain r 4 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (colEnd_ok ws R.t H CH (d == 0) (k := d + 4) ho8 ho (by omega) (tne H hH).1 (tne H hH).2 t3
    Hlh (fun e => nZ (e ▸ lo_mem hH)) (nmem hH nM) (fun e => x3w (e ▸ lo_mem hH))
    (fun e => x3w (e ▸ hi_mem hH)) (fun e => x12w (e ▸ lo_mem hH)) (fun e => x12w (e ▸ hi_mem hH))
    wM wZ wH hcH h0H (hfit.high d hd)) fun x ⟨xm, xc, xk⟩ => ?_
  have hnot : ∀ {q : Reg}, q ∉ writes R accs → q ≠ CH → q ∉ [H.lo, H.hi, R.t, CH] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ lo_mem hH)
    · exact hq (h ▸ hi_mem hH)
    · exact hq (h ▸ t_mem)
    · exact hc h
  have rad : ∀ n, n % radix < 2 ^ 64 := fun n => Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have tw : Outside base o 64 t.mem x.mem := by
    rw [xm, wm, um]
    exact (stage_outside _ _ ho (by omega) _).trans (stage_outside _ _ ho (by omega) _)
  have sub : ∀ q ∈ writes R accs, q ∈ colWrites R accs := fun q h => List.mem_append_left _ h
  refine ⟨⟨ws.of_keeps xk ⟨hnot x3w (fun e => h3 (by simp [e])), hnot x12w (fun e => h12 (by simp [e]))⟩,
    by rw [xk.1 _ (hnot nM (fun e => hM (by simp [colWrites, e]))), wM],
    by rw [xk.1 _ (hnot nZ (fun e => hZ (by simp [colWrites, e]))), wZ],
    hi.out.trans tw, fun k hk => ?_, fun k hk => ?_, fun _ => ?_, fun _ => ?_⟩,
    (uk.mono sub).trans ((wk.mono ?_).trans (xk.mono ?_)), tw⟩
  · rw [xm, word_stage ho (by omega) (by omega), ite_eq_right (by omega), wm, word_stage ho (by omega) (by omega)]
    by_cases h : k = d
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), h]
      simp only [chainLimb, Nat.zero_add]
    · rw [ite_eq_right h, um]; exact hi.lo k (by omega)
  · rw [xm, show 4 + k = k + 4 by omega, word_stage ho (by omega) (by omega)]
    by_cases h : k + 4 = d + 4
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), show k = d by omega]
      simp only [chainLimb]
    · rw [ite_eq_right h, wm, word_stage ho (by omega) (by omega), ite_eq_right (by omega), um,
        show k + 4 = 4 + k by omega]
      exact hi.hi k (by omega)
  · rw [xk.1 _ (hnot hCL hCC), wc]
    simp only [chain, Nat.zero_add]
  · rw [xc]
    simp only [chain]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ lo_mem hL)
    · exact sub _ (h ▸ hi_mem hL)
    · exact sub _ (h ▸ t_mem)
    · rw [h]; simp [colWrites]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ lo_mem hH)
    · exact sub _ (h ▸ hi_mem hH)
    · exact sub _ (h ▸ t_mem)
    · rw [h]; simp [colWrites]

theorem columns_ok (hG : Good R accs) (hC : ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192)
    (hfit : Fits r) (hops : ∀ d < 4, (col d).all (opOk (writes R accs) accs) = true)
    (P : State → Prop)
    (hP : ∀ t u, P t → Keeps (colWrites R accs) t u → Outside base o 64 t.mem u.mem → P u)
    (hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      sem (srcVal t base b) e (col d) L = r d ∧ sem (srcVal t base b) e (col d) H = r (d + 4))
    {s : State} (hs : Scr s base) (hP0 : P s) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hz : s.gpr ZERO = 0) :
    WP isa (.block (columns R b L H col o)) s fun t =>
      P t ∧ ColInv base o r s t 4 ∧ Keeps (colWrites R accs) s t := by
  let inv := fun n (t : State) => P t ∧ ColInv base o r s t n ∧ Keeps (colWrites R accs) s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tp, ti, tk⟩ => ?_) 4 (by decide) s
    ⟨hP0, ⟨hs, hm, hz, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
      fun h => absurd h (Nat.lt_irrefl _)⟩, Keeps.refl _ _⟩
  exact WP.mono (column_ok hG hC hL hH hLH hb8 hb ho8 ho hfit hn (hops n hn) ti (hsem n hn t tp))
    fun u ⟨ui, uk, uo⟩ => ⟨hP t u tp uk uo, ui, tk.trans uk⟩

end

end VG.Proof.Curve448.AArch64.Fast
