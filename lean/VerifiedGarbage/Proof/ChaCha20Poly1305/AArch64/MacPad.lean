import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Prologue
import Mathlib.Tactic.NormNum.Basic

/-!
# ChaCha20-Poly1305 on AArch64: absorbing padded data

Untrusted: everything here is checked by Lean. `macPad p n` absorbs the `n`
bytes at `p` into the Poly1305 state, and zeros to a multiple of 16:
`msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_subImm wp_mov wp_movz wp_sub wp_lsr wp_ldrb
  wp_strb wp_str eval_zero eval_nonzero_ofNat ofNat_beq_zero sub_ofNat add_ofNat writeW8_apply)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .x24 ∨ p = .x22) ∧ (n = .x25 ∨ n = .x23)

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len w : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x w) : (⟨P, len⟩ : Region).Contains x w := by
  simp only [Region.Contains] at *
  have : (x - P).toNat ≤ (x - (P + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - P = (x - (P + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem Src.cov_sub {s₀ : State} {P : Addr} {len : Nat} (hs : Src s₀ P len) {a n : Nat} (h : a + n ≤ len)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers [⟨P + BitVec.ofNat 64 a, n⟩] (s.rd ++ s.wr) := by
  intro x w ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [hrd, hwr]
  exact hs.cov x w ⟨_, List.mem_singleton_self _, contains_off_sub h hc⟩

theorem Src.disj_sub {P : Addr} {len : Nat} {R : Region} (hd : R.Disjoint ⟨P, len⟩) {a n : Nat}
    (h : a + n ≤ len) : R.Disjoint ⟨P + BitVec.ofNat 64 a, n⟩ :=
  fun x h₁ h₂ => hd x h₁ (contains_off_sub h h₂)

theorem MacRegs.p_ne {p n : Reg} (hr : MacRegs p n) :
    p ≠ .x0 ∧ p ≠ .x1 ∧ p ≠ .x2 ∧ p ≠ .x9 ∧ p ≠ .x10 ∧ p ∈ preserved ∧ p ≠ .x30 := by
  rcases hr.1 with rfl | rfl <;> decide

theorem MacRegs.n_ne {p n : Reg} (hr : MacRegs p n) :
    n ≠ .x0 ∧ n ≠ .x1 ∧ n ≠ .x2 ∧ n ≠ .x9 ∧ n ≠ .x10 ∧ n ∈ preserved ∧ n ≠ .x30 := by
  rcases hr.2 with rfl | rfl <;> decide

/-! ## The whole blocks -/

theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = s.gpr p ∧ s'.gpr .x2 = s.gpr n >>> 4 ∧
      Kept [] s s' := by
  have hp := hr.p_ne
  have hn := hr.n_ne
  have h : WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = s.gpr p ∧ s'.gpr .x2 = s.gpr n >>> 4 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ hp.1],
        by rw [u₃.gpr, u₂.other _ hn.2.1, u₁.other _ hn.1],
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [mov, dstOf, preserved])) fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `(x << 60) >> 60` is `x mod 16`. -/
theorem shl_shr60 (x : BitVec 64) : (x <<< 60) >>> 60 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_ofNat_lt (by omega),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 16 * 2 ^ 60 by norm_num, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by norm_num)]

theorem macC_ok (n : Reg) (s : State) :
    WP isa (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60]) s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr n).toNat % 16) ∧ Kept [] s s' := by
  have h : WP isa (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60]) s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr n).toNat % 16) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_lsl (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.gpr, shl_shr60], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
        by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h10, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h10, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) s fun s' =>
      s'.gpr .x1 = s.gpr p + (s.gpr n - s.gpr .x10) ∧ (∀ r, r ≠ .x9 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      Kept [] s s' := by
  have hp := hr.p_ne
  have h : WP isa (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) s fun s' =>
      s'.gpr .x1 = s.gpr p + (s.gpr n - s.gpr .x10) ∧ (∀ r, r ≠ .x9 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_sub fun s₁ u₁ => wp_add fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.other _ hp.2.2.2.1, u₁.gpr],
        fun r h₁ h₂ => by rw [u₂.other _ h₂, u₁.other _ h₁],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h1, hg', hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h1, hg', Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `x0 = x21 + a`, `x1 = x21 + b` and `x2 = v`. -/
theorem ptrs3_ok {a b : Nat} (ha : a < 4096) (hb : b < 4096) (v : BitVec 16) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b, .movz .x .x2 v 0]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧
      s'.gpr .x2 = v.setWidth 64 ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b, .movz .x .x2 v 0]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧ s'.gpr .x2 = v.setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm ha fun s₁ u₁ => wp_addImm hb fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)], u₃.gpr,
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-! ## Zeroing the padded block -/

theorem zero16 : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 := rfl

theorem padZ_ok {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.movz .x .x11 0 0, .str .x .x11 .x21 576, .str .x .x11 .x21 584,
      .addImm .x .x9 .x21 576]) s fun s' =>
      s'.gpr .x9 = off (cx s₀) 576 ∧ (∀ r, r ≠ .x11 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (576 + j)) = 0 := by
  have o0 := hp.in_ctx (a := 576) (w := 8) (by omega)
  have o1 := hp.in_ctx (a := 584) (w := 8) (by omega)
  rw [← hwr] at o0 o1
  refine wp_movz fun s₁ u₁ => ?_
  refine wp_str (a := off (cx s₀) 576) (by decide) (by rw [u₁.other _ (by decide), hx21])
    (by rw [u₁.wr]; exact o0) fun s₂ g₂ => ?_
  refine wp_str (a := off (cx s₀) 584) (by decide) (by rw [g₂.gpr, u₁.other _ (by decide), hx21])
    (by rw [g₂.wr, u₁.wr]; exact o1) fun s₃ g₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => WP.block_nil ?_
  have x11 : s₁.gpr .x11 = 0 := u₁.gpr
  have hm : s₄.mem = (s.mem.writeW (off (cx s₀) 576) (0 : BitVec 64)).writeW (off (cx s₀) 584)
      (0 : BitVec 64) := by
    rw [u₄.mem, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x11]
  refine ⟨by rw [u₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ (by decide), hx21],
    fun r h₁ h₂ => by rw [u₄.other _ h₂, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr], ?_, fun j hj => ?_⟩
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · rw [hm, VG.Proof.Poly1305.writeW64_zero_apply, VG.Proof.Poly1305.writeW64_zero_apply]
    have e : ∀ d, d ≤ 576 + j → (off (cx s₀) (576 + j) - off (cx s₀) d).toNat = 576 + j - d := by
      intro d hd
      rw [show off (cx s₀) (576 + j) - off (cx s₀) d = BitVec.ofNat 64 (576 + j - d) by
          show cx s₀ + BitVec.ofNat 64 (576 + j) - (cx s₀ + BitVec.ofNat 64 d) = _
          rw [show 576 + j = d + (576 + j - d) by omega, BitVec.ofNat_add]; bv_omega,
        toNat_ofNat_lt (by omega)]
    by_cases h : 8 ≤ j
    · rw [e 584 (by omega)]
      simp only [show 576 + j - 584 < 8 by omega, ite_true]
    · have w : ¬ (off (cx s₀) (576 + j) - off (cx s₀) 584).toNat < 8 := by
        rw [show off (cx s₀) (576 + j) - off (cx s₀) 584 = BitVec.ofNat 64 (2 ^ 64 - 8 + j) by
          show cx s₀ + BitVec.ofNat 64 (576 + j) - (cx s₀ + BitVec.ofNat 64 584) = _
          bv_omega, toNat_ofNat_lt (by omega)]
        omega
      simp only [w, ite_false, e 576 (by omega), show 576 + j - 576 < 8 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (t i : Nat) (s : State) : Prop where
  x1 : s.gpr .x1 = Q + BitVec.ofNat 64 i
  x9 : s.gpr .x9 = off (cx s₀) (576 + i)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (576 + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.ldrb .x11 .x1 0, .strb .x11 .x9 0, .addImm .x .x1 .x1 1, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem off_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) : off p a ≠ off p b := by
  intro he
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have e := congrArg (· - p) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  exact h this

theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr) (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s (CpInv s₀ s₂ Q t (i + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (576 + i)) 1 := by rw [h.wr, hwr]; exact hp.in_ctx (by omega)
  have core : WP isa (.block copyBody) s fun s' =>
      s'.gpr .x1 = Q + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .x9 = off (cx s₀) (576 + (i + 1)) ∧
      s'.gpr .x10 = BitVec.ofNat 64 (t - (i + 1)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off (cx s₀) (576 + i)) (s.mem (Q + BitVec.ofNat 64 i)) := by
    unfold copyBody
    refine wp_ldrb (a := Q + BitVec.ofNat 64 i) (by decide) (by rw [h.x1]; exact BitVec.add_zero _) hin
      fun s₁ u₁ => ?_
    refine wp_strb (a := off (cx s₀) (576 + i)) (by decide)
      (by rw [u₁.other _ (by decide), h.x9]; exact BitVec.add_zero _) (by rw [u₁.wr]; exact hout)
      fun s₂' g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
      wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x1,
        add_ofNat]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x9]
      exact add_ofNat _ _ _
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x10,
        sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
    · rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine WP.mono (WP.kept core (by simp [copyBody, dstOf, preserved]))
    fun s' ⟨⟨h1, h9, h10, hrd, hwr', hm⟩, hg, hsp⟩ => ⟨h1, h9, h10, fun r hr => by rw [hg r hr, h.keep r hr],
      by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr', h.wr], ?_, fun k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => hdisj i hi r hr _ (by
        simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, hbyte]
    · simp only [off_ne (cx s₀) (a := 576 + k) (b := 576 + i) (by omega) (by omega) (by omega), ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) 576 + BitVec.ofNat 64 k = off (cx s₀) (576 + k) from off_off _ _ _, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

/-- The frame of the Poly1305 state and the padded block. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144]

theorem sub_mac (s₀ : State) {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) :
    Region.Sub (sub s₀ k n) (sub s₀ 448 144) := by
  intro x hx
  simp only [Region.Contains] at *
  bv_omega

theorem kept_mac {s₀ s s' : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592)
    (hk : Kept [sub s₀ k n] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩

theorem kept_mac0 {s₀ s s' : State} (hk : Kept [] s s') : Kept (macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem padTail_eq : padTail =
    .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 576, .str .x .x11 .x21 584, .addImm .x .x9 .x21 576])
    (.seq (.loop (.block copyBody) (.nonzero .x .x10))
    (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 576, .movz .x .x2 1 0])
      (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks))) := rfl

theorem padTail_ok {s₀ : State} (hp : APre s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hx1 : s.gpr .x1 = Q) (hx10 : s.gpr .x10 = BitVec.ofNat 64 t) (hx21 : s.gpr .x21 = cx s₀)
    (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 576 16)) :
    WP isa padTail s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono (WP.withSp (padZ_ok hp hx21 hwr)) fun s₂ ⟨⟨x9₂, g₂, rd₂, wr₂, f₂, z₂⟩, sp₂⟩ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .x .x10) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .x .x10) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI)
        fun s' h' => ?_
      have hz := eval_nonzero_ofNat s' .x10 (by omega) h'.x10
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), hx1]; simp,

      by rw [x9₂], by rw [g₂ _ (by decide) (by decide), hx10]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 576) (by omega) (by omega) 1 s₃)
    fun s₄ ⟨h0, h1, h2, k₄⟩ => ?_)
  have x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [h₃.keep _ (by decide), g₂ _ (by decide) (by decide), hx21]
  rw [x21₃] at h0 h1
  have wr₄ : s₄.wr = s₀.wr := by rw [k₄.wr, h₃.wr, wr₂, hwr]
  have mm₄ : s₄.mem = s₃.mem := k₄.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by omega)
    (sub_disj s₀ (b := 576) (m := 16 * 1) (by omega) (by omega) (by omega))
    (by rw [hp.off_toNat (by omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₄ (a := 448) (n := 128) (b := 576) (m := 16 * 1) (by omega) (by omega))
    (covers1 hp wr₄ (a := 448) (n := 128) (by omega)) fun s₅ k₅ repr₅ => ?_
  have k₃ : Kept [sub s₀ 576 16] s s₃ :=
    ⟨fun r hr h30 => by
        rw [h₃.keep r hr, g₂ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)],
      by rw [h₃.sp, sp₂], by rw [h₃.rd, rd₂], by rw [h₃.wr, wr₂], f₂.trans h₃.frame⟩
  refine ⟨(kept_mac (by omega) (by omega) k₃).trans ((kept_mac0 k₄).trans (kept_mac (k := 448) (n := 128)
    (by omega) (by omega) k₅)), fun key msg hr => ?_⟩
  have f26 : Frame [sub s₀ 576 16] s.mem s₄.mem := by rw [mm₄]; exact k₃.frame
  have hr₄ : Repr s₄.mem (off (cx s₀) 448) key msg := Repr.frame f26 (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by omega) (by omega) (by omega)) hr
  have hb : bytesAt s₄.mem (off (cx s₀) 576) (16 * 1) = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
    rw [mm₄, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
    refine congrArg (· ++ _) ?_
    simp only [bytesAt]
    apply List.map_congr_left
    intro j hj
    exact src₂ j (List.mem_range.mp hj)
  have := repr₅ key msg hr₄
  rwa [hb] at this

/-! ## The whole of `macPad` -/

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad p n) s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpn := hr.p_ne
  have hnn := hr.n_ne
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono (macA_ok hr s) fun s₁ ⟨x0₁, x1₁, x2₁, k₁⟩ => ?_)
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  refine WP.seq (blocks_call (P := off (cx s₀) 448) (p := P) (n := len / 16)
    (by rw [x0₁, hx21]) (by rw [x1₁, hP]) (by rw [x2₁, hn, shr4_ofNat hlt]) (by omega)
    ((hcP.sub_left (sub_ctx s₀ (by omega))).sub_right (Region.sub_prefix hk))
    (by have := hs.wrap; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [k₁.rd, k₁.wr, hrd, hwr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · exact covers1 hp (by rw [k₁.wr, hwr]) (a := 448) (n := 128) (by omega) a w
          ⟨_, List.mem_singleton_self _, hc⟩ |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (covers1 hp (by rw [k₁.wr, hwr]) (a := 448) (n := 128) (by omega))
    fun s₂ k₂ repr₂ => ?_)
  have m₁ := k₁.mem_eq
  rw [m₁] at repr₂
  refine WP.seq (WP.mono (macC_ok n s₂) fun s₃ ⟨x10₃, k₃⟩ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 64 len := by
    rw [k₂.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, k₁.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, hn]
  have p₂ : s₂.gpr p = P := by
    rw [k₂.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, k₁.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, hP]
  rw [n₂, toNat_ofNat_lt hlt] at x10₃
  have k₁₃ : Kept (macR s₀) s s₃ :=
    (kept_mac0 k₁).trans ((kept_mac (k := 448) (n := 128) (by omega) (by omega) k₂).trans (kept_mac0 k₃))
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₃ := k₃.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      have e : isa.eval (.zero .x .x10) s₃ = some (s₃.gpr .x10 == 0) := eval_zero s₃ .x10
      rw [e, x10₃, ofNat_beq_zero (by omega)]) (fun h => ?_) (fun h => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨k₁₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using h
    refine WP.seq (WP.mono (macD_ok hr s₃) fun s₄ ⟨x1₄, g₄, k₄⟩ => ?_)
    have hQ : s₄.gpr .x1 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [x1₄, x10₃, k₃.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, n₂, k₃.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, p₂,
        sub_ofNat (by omega), show len - len % 16 = 16 * (len / 16) by omega]
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [add_ofNat]
      exact hs.cov_sub (a := 16 * (len / 16) + j) (n := 1) (by omega)
        (by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd, hrd]) (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hwr]) _ _
        ⟨_, List.mem_singleton_self _, self_contains _⟩
    have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ 576 16) := fun j hj => by
      rw [add_ofNat]
      exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by omega))) (a := 16 * (len / 16) + j) (n := 1)
        (by omega)).symm
    refine WP.mono (padTail_ok hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by omega) (by omega) hQ
      (by rw [g₄ _ (by decide) (by decide), x10₃])
      (by rw [k₄.cs _ (pres .x21) (pres30 .x21), k₃.cs _ (pres .x21) (pres30 .x21),
        k₂.cs _ (pres .x21) (pres30 .x21), k₁.cs _ (pres .x21) (pres30 .x21), hx21])
      (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hwr])
      hsrc hdj) fun s₅ ⟨k₅, repr₅⟩ => ?_

    refine ⟨k₁₃.trans ((kept_mac0 k₄).trans k₅), fun key msg hr => ?_⟩
    have m₄ := k₄.mem_eq
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, bytesAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hcP.sub_left (sub_ctx s₀ (by omega))).sub_right
          (sub_off P (a := 16 * (len / 16)) (by omega))).symm) (by omega), m₁] at this

    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.AArch64
