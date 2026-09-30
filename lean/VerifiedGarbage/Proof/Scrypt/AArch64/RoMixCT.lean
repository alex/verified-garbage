import VerifiedGarbage.Proof.Scrypt.AArch64.Common
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.AArch64.Lit

/-!
# scryptROMix on AArch64: the precondition

Untrusted: everything here is checked by Lean. The regions the function
works on, and `BlockMixSpec`: what a call of `vg_scrypt_blockmix` does (the
verified one meets it: `Proof/Scrypt/AArch64/RoMixCT.lean`).
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c` writes scryptBlockMix of the `128 r` bytes at `x0` to `x2`,
with the 128 bytes at `x4` as working space and the 16 bytes below the stack
pointer as its frame. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : Addr) (r : Nat), s.gpr .x0 = src → s.gpr .x1 = BitVec.ofNat 64 r →
    s.gpr .x2 = dst → s.gpr .x3 = BitVec.ofNat 64 r → s.gpr .x4 = scr → 0 < r →
    128 * r < 2 ^ 64 →
    Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩ → Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩ →
    Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩ → 16 ≤ s.sp.toNat →
    (below s.sp 16).Disjoint ⟨src, 128 * r⟩ → (below s.sp 16).Disjoint ⟨dst, 128 * r⟩ →
    (below s.sp 16).Disjoint ⟨scr, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 64 → dst.toNat + 128 * r ≤ 2 ^ 64 → scr.toNat + 128 ≤ 2 ^ 64 →
    InRegions (s.rd ++ s.wr) src (128 * r) → InRegions s.wr dst (128 * r) →
    InRegions s.wr scr 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
        Frame [⟨dst, 128 * r⟩, ⟨scr, 128⟩, below s.sp 16] s.mem s'.mem →
        bytesAt s'.mem dst (128 * r) = blockMix r (bytesAt s.mem src (128 * r)) → Q s') →
    WP isa (.call "vg_scrypt_blockmix" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev rr : Nat := (s₀.gpr .x1).toNat
abbrev vP : Addr := s₀.gpr .x2
abbrev vl : Nat := (s₀.gpr .x3).toNat
abbrev sc : Addr := s₀.gpr .x4
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vP s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, (rr s₀ + 2) * 128⟩
/-- The frames of our calls. -/
abbrev stkR : Region := below s₀.sp 16
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)
/-- `V[i]`. -/
abbrev vAt (i : Nat) : Addr := vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := sc s₀ + BitVec.ofNat 64 192

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ rmSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, vR s₀, scR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  v_s : (vR s₀).Disjoint (scR s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_v : (stkR s₀).Disjoint (vR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 64
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo
  x5 : (s₀.gpr .x5).toNat = rr s₀ + 2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp only [h16] at h2 h4 h5 h9 h12
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_, h15, h16⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h14)).symm

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

theorem vl_mul : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by
  rw [hp.vl_eq, Nat.mul_comm, ← Nat.mul_assoc]

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 64 := by
  rw [← vl_mul hp]
  by_contra hc
  refine hp.v_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (sc s₀ - vP s₀).isLt
  omega

theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem NN_lt : NN s₀ < 2 ^ 64 := by
  have := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  omega

omit hp in
theorem v_le {i : Nat} (hi : i < NN s₀) : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- `V[i]` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  have := v_le hi
  show Region.Sub ⟨vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vP s₀, vl s₀ * 128⟩
  exact sub_off (by rw [vl_mul hp]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have h1 := v_le hi
  have h2 := v_le hk
  refine disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  · right; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (scR s₀) := by
  have := hp.s_nw
  exact sub_off (by omega) (by omega)

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨sc s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨sc s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := disj_off (sc s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 192)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 128, 64⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (sc s₀ + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 192) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← add_ofNat]
  exact sub_off (by omega) (by omega)

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : 128 ≤ p.2 ∧ p.2 + 8 ≤ 184 := by
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := saved_offs hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega) (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_stk : (keepR s₀).Disjoint (stkR s₀) := hp.stk_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem keep_w : (keepR s₀).Disjoint ⟨sc s₀, 128⟩ := by
  have := disj_off (sc s₀) (o₁ := 128) (n₁ := 64) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact disj_off (sc s₀) (o₁ := 128) (n₁ := 64) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega)
    (by omega) (by omega) (by omega) (by omega)

omit hp in
theorem b_sub' : Region.Sub ⟨bP s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

theorem shl_ofNat {a : Nat} (n : Nat) (h : a * 2 ^ n < 2 ^ 64) :
    BitVec.ofNat 64 a <<< n = BitVec.ofNat 64 (a * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _
    (Nat.two_pow_pos n)) h), Nat.shiftLeft_eq, Nat.mod_eq_of_lt h, toNat_ofNat_lt h]

end VG.Proof.Scrypt.AArch64.RoMix

/-!
# scryptROMix on AArch64: the small loops

Untrusted: everything here is checked by Lean. The word copy (`copyLoop`),
the word exclusive-or (`xorLoop`) and the computation of `2 N` by doubling
(`nLoop`). The memory lemmas are shared with the other targets
(`Proof/Scrypt/Memory.lean`).
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_add wp_sub wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero ofNat_pred sub_beq)
open VG.Proof.Scrypt.AArch64.BlockMix (wp_eor)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat)

/-! ## Arithmetic -/

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega), Nat.sub_sub]

theorem dec_ne {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  rw [bne, ofNat_beq_zero (by omega)]
  by_cases h : k + 1 = n
  · simp only [h, Nat.sub_self, decide_true, Bool.not_true, ne_eq, not_true_eq_false, decide_false]
  · simp only [show n - (k + 1) ≠ 0 by omega, decide_false, Bool.not_false, ne_eq, h,
      not_false_eq_true, decide_true]

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (8 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop on `cbnz cr` that runs its body `n > 0` times: the
register is zero exactly after the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by
    show VG.AArch64.eval (.nonzero .x cr) s' = _
    rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.gpr r = s.gpr r
  x9 : t.gpr .x9 = src + BitVec.ofNat 64 (8 * k)
  x10 : t.gpr .x10 = dst + BitVec.ofNat 64 (8 * k)
  x11 : t.gpr .x11 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block [.ldr .x .x12 .x9 0, .str .x .x12 .x10 0, .addImm .x .x9 .x9 8,
      .addImm .x .x10 .x10 8, .subImm .x .x11 .x11 1]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ (t'.gpr .x11 != 0) = decide (k + 1 ≠ n) := by
  refine wp_ldr (a := src + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [h.x9, add_zero'])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_str (a := dst + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.x10, add_zero'])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ u₂ => ?_
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ =>
    wp_subImm (by decide) fun t₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x12 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
  have e11 : t₅.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.x11, dec_count hk]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], fun r h9 h10 h11 h12 => ?_, ?_, ?_, e11, ?_⟩, ?_⟩
  · rw [u₅.other r h11, u₄.other r h10, u₃.other r h9, g r h12, h.other r h9 h10 h11 h12]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.x9, next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.x10, next_ptr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Scrypt.Memory.copy_mem s.mem src dst k 8
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)
  · rw [e11, dec_ne hk (by omega)]

/-- `copyLoop` copies `8 n` bytes from `x9` to `x10` (`x11 = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (h9 : s.gpr .x9 = src) (h10 : s.gpr .x10 = dst) (h11 : s.gpr .x11 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h9], by rw [ofNat_zero_add, h10],
    by rw [h11, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
    t.gpr r = s.gpr r
  x9 : t.gpr .x9 = x + BitVec.ofNat 64 (8 * k)
  x10 : t.gpr .x10 = y + BitVec.ofNat 64 (8 * k)
  x11 : t.gpr .x11 = d + BitVec.ofNat 64 (8 * k)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * k)) (bytesAt s.mem y (8 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.ldr .x .x13 .x9 0, .ldr .x .x14 .x10 0, .logic .eor .x .x13 .x13 .x14,
      .str .x .x13 .x11 0, .addImm .x .x9 .x9 8, .addImm .x .x10 .x10 8, .addImm .x .x11 .x11 8,
      .subImm .x .x12 .x12 1]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ (t'.gpr .x12 != 0) = decide (k + 1 ≠ n) := by
  refine wp_ldr (a := x + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [h.x9, add_zero'])
    (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_ldr (a := y + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.x10, add_zero'])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_eor fun t₃ u₃ => ?_
  refine wp_str (a := d + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x11,
      add_zero'])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ u₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ =>
    wp_addImm (by decide) fun t₇ u₇ => wp_subImm (by decide) fun t₈ u₈ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x13 → r ≠ .x14 → t₄.gpr r = t.gpr r := fun r h13 h14 => by
    rw [u₄.gpr, u₃.other r h13, u₂.other r h14, u₁.other r h13]
  have e12 : t₈.gpr .x12 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x12, dec_count hk]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h9 h10 h11 h12 h13 h14 => ?_, ?_, ?_, ?_, e12, ?_⟩, ?_⟩
  · rw [u₈.other r h12, u₇.other r h11, u₆.other r h10, u₅.other r h9, g r h13 h14,
      h.other r h9 h10 h11 h12 h13 h14]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g _ (by decide) (by decide), h.x9, next_ptr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x10, next_ptr]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x11, next_ptr]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .x13 (by decide), u₂.gpr,
      u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact Proof.Scrypt.Memory.xor_mem s.mem hk hlt hdx hdy
  · rw [e12, dec_ne hk (by omega)]

/-- `xorLoop` writes `[x9] xor [x10]` to `x11`, `8 n` bytes (`x12 = n > 0` words). -/
theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (h9 : s.gpr .x9 = x) (h10 : s.gpr .x10 = y) (h11 : s.gpr .x11 = d)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h9],
    by rw [ofNat_zero_add, h10], by rw [ofNat_zero_add, h11], by rw [h12, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .x9 → r' ≠ .x10 → r' ≠ .x12 → t.gpr r' = s.gpr r'
  x9 : t.gpr .x9 = BitVec.ofNat 64 (r * 2 ^ k)
  x10 : t.gpr .x10 = BitVec.ofNat 64 (2 ^ k)

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.add .x .x9 .x9 .x9, .add .x .x10 .x10 .x10, .sub .x .x12 .x9 .x11]) t
      fun t' => NInv s r (k + 1) t' ∧ (t'.gpr .x12 != 0) = decide (k + 1 ≠ e + 1) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_sub fun t₃ u₃ => WP.block_nil ?_
  have ax : t₂.gpr .x9 = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.x9, Proof.Scrypt.Memory.dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₃.mem, u₂.mem, u₁.mem, h.mem],
    fun r' h9 h10 h12 => ?_, by rw [u₃.other _ (by decide), ax], ?_⟩, ?_⟩
  · rw [u₃.other r' h12, u₂.other r' h10, u₁.other r' h9, h.other r' h9 h10 h12]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x10, ← Nat.one_mul (2 ^ k),
      Proof.Scrypt.Memory.dbl_pow, Nat.one_mul]
  · rw [u₃.gpr, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide) (by decide), h11, bne, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, Bool.not_false, ne_eq, hh, not_false_eq_true, decide_true]

/-- `nLoop` doubles `x9` (from `r`) and `x10` (from 1) until `x9 = x11 = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 r) (h10 : s.gpr .x10 = 1)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .x9 → r' ≠ .x10 → r' ≠ .x12 → s'.gpr r' = s.gpr r') ∧
      s'.gpr .x10 = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h11 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.sp, h.mem, h.other, h.x10⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, by rw [h9, Nat.pow_zero, Nat.mul_one],
    by rw [h10]; rfl⟩

end VG.Proof.Scrypt.AArch64.RoMix

/-!
# scryptROMix on AArch64: correctness

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers and our return address in `scratch` and computes `N`;
step 2 and step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`); the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str wp_movz
  wp_lsr wp_and readW_writeW_save)
open VG.Proof.Scrypt.AArch64.BlockMix (wp_lsl)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  InRegions.of_mem InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep
  bytesAt_length xorBytes_length)

/-! ## Instructions -/

theorem wp_madd {is : List Instr} {s : State} {Q : State → Prop} {d n m a : Reg}
    (k : ∀ s', Upd s s' d (s.gpr a + s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.madd .x d n m a :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr a + s.gpr n * s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.MdStream.AArch64.Upd.write64 _ _ _))

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem shl7 {x : BitVec 64} (h : 128 * x.toNat < 2 ^ 64) : x <<< 7 = BitVec.ofNat 64 (128 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 7 = 128 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt h, toNat_ofNat_lt h]

theorem dbl' (x : BitVec 64) : x + x = BitVec.ofNat 64 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat' x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 128) (s₀.gpr .x19)).writeW
    (sc s₀ + BitVec.ofNat 64 136) (s₀.gpr .x20)).writeW (sc s₀ + BitVec.ofNat 64 144)
    (s₀.gpr .x22)).writeW (sc s₀ + BitVec.ofNat 64 152) (s₀.gpr .x23)).writeW
    (sc s₀ + BitVec.ofNat 64 160) (s₀.gpr .x24)).writeW (sc s₀ + BitVec.ofNat 64 168)
    (s₀.gpr .x30)).writeW (sc s₀ + BitVec.ofNat 64 176) (s₀.gpr .x21)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 136 (by omega))).writeW (List.mem_singleton_self _) _
    (c 144 (by omega))).writeW (List.mem_singleton_self _) _ (c 152 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 160 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 168 (by omega))).writeW (List.mem_singleton_self _) _ (c 176 (by omega))

theorem prologue_eq : rmPrologue =
    ([.str .x .x19 .x4 128, .str .x .x20 .x4 136, .str .x .x22 .x4 144, .str .x .x23 .x4 152,
     .str .x .x24 .x4 160, .str .x .x30 .x4 168, .str .x .x21 .x4 176] : List Instr) ++
    [mov .x19 .x0, mov .x20 .x2, mov .x21 .x4, .lsl .x .x22 .x1 7,
     mov .x9 .x1, .movz .x .x10 1 0, .add .x .x11 .x3 .x3] := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.str .x .x19 .x4 128, .str .x .x20 .x4 136, .str .x .x22 .x4 144,
      .str .x .x23 .x4 152, .str .x .x24 .x4 160, .str .x .x30 .x4 168, .str .x .x21 .x4 176] : List Instr) ++
      rest)) s₀ Q := by
  have o : ∀ d, d + 8 ≤ 256 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (o 128 (by omega) _ rfl) fun s1 u1 => ?_
  refine wp_str (by decide) (by rw [u1.gpr]) (o 136 (by omega) _ u1.wr) fun s2 u2 => ?_
  refine wp_str (by decide) (by rw [u2.gpr, u1.gpr]) (o 144 (by omega) _ (u2.wr.trans u1.wr))
    fun s3 u3 => ?_
  refine wp_str (by decide) (by rw [u3.gpr, u2.gpr, u1.gpr])
    (o 152 (by omega) _ (u3.wr.trans (u2.wr.trans u1.wr))) fun s4 u4 => ?_
  refine wp_str (by decide) (by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 160 (by omega) _ (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))) fun s5 u5 => ?_
  refine wp_str (by decide) (by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 168 (by omega) _ (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    fun s6 u6 => ?_
  refine wp_str (by decide) (by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 176 (by omega) _ (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr))))))
    fun s7 u7 => ?_
  exact k s7 (by rw [u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (by rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (u7.wr.trans (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr))))))
    (by rw [u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp])
    (by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u6.gpr, u5.gpr, u4.gpr, u3.gpr,
          u2.gpr, u1.gpr]
        rfl)

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x9 : s.gpr .x9 = BitVec.ofNat 64 (rr s₀)
  x10 : s.gpr .x10 = 1
  x11 : s.gpr .x11 = BitVec.ofNat 64 (2 * vl s₀)

theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x19 .x0, mov .x20 .x2, mov .x21 .x4, .lsl .x .x22 .x1 7,
     mov .x9 .x1, .movz .x .x10 1 0, .add .x .x11 .x3 .x3]) s₁ (P1 s₀) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_lsl (by decide) fun d ud =>
    wp_mov fun e ue => wp_movz fun f uf => wp_add fun h uh => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uh.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [uh.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [uh.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, shl7 lt]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g]
    exact ofNat_toNat' _
  · rw [uh.other _ (by decide), uf.gpr]; decide
  · rw [uh.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, dbl']

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 64 := by have := vl_mul hp; omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.x9 h.x10
    (by rw [h.x11, e2])) fun t ⟨rd, wr, sp, mem, oth, x10⟩ => ?_
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp], by rw [mem, h.mem],
    by rw [oth _ (by decide) (by decide) (by decide), h.x19],
    by rw [oth _ (by decide) (by decide) (by decide), h.x20],
    by rw [oth _ (by decide) (by decide) (by decide), h.x21],
    by rw [oth _ (by decide) (by decide) (by decide), h.x22],
    by rw [x10, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (NN s₀ - i)
  x24 : s.gpr .x24 = vAt s₀ i
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

set_option simprocs false in
theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 184) (BitVec.ofNat 64 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have ho := saved_offs hp
  rw [readW_writeW_save _ _ _ (by omega) (by decide) (by omega)]
  exact saveMem_saved s₀ p hp

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 64 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_lsr (by decide) fun t1 u1 => ?_
  have hd : t1.gpr .x10 = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.x10, shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_str (a := sc s₀ + BitVec.ofNat 64 184) (by decide) (by rw [u1.other _ (by decide), h.x21])
    (by rw [u1.wr, h.wr, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 u2 => wp_mov fun t3 u3 => wp_mov fun t4 u4 => WP.block_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x23 → r ≠ .x24 → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, u2.gpr, u1.other _ b]
  have hm : t4.mem = (saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 184) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, u2.mem, hd, u1.mem, h.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp],
    by rw [g _ (by decide) (by decide) (by decide), h.x19],
    by rw [g _ (by decide) (by decide) (by decide), h.x20],
    by rw [g _ (by decide) (by decide) (by decide), h.x21],
    by rw [g _ (by decide) (by decide) (by decide), h.x22], ?_, ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.gpr, hd]; rfl
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.x20]
    simp
  · refine frame_bytesAt fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `x0` is set. -/
abbrev bmTail : List Instr := [.lsr .x .x1 .x22 7, mov .x2 .x19, mov .x3 .x1, mov .x4 .x21]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (sc s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The registers our loops keep are not the call's arguments. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x9 ∧
    r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 := by decide

/-- Setting up and making the call, from `x0 = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .x0 = A) (h19 : s.gpr .x19 = bP s₀) (h21 : s.gpr .x21 = sc s₀)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩)
    (hAs : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_lsr (by decide) fun a ua => wp_mov fun b ub => wp_mov fun d ud => wp_mov fun e ue =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → e.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ue.other _ h4, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .x1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h22, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  have hm : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have hsp' : e.sp = s₀.sp := by rw [ue.sp, ud.sp, ub.sp, ua.sp, hsp]
  refine hS e A (bP s₀) (sc s₀) (rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), h1])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h19])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), h1])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h21])
    hp.pos lt ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hp.sp16)
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [ue.rd, ud.rd, ub.rd, ua.rd, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact w_in hp) _
    fun s' rd' wr' sp' cs' f' b' => hQ s' (by rw [rd', ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', ue.wr, ud.wr, ub.wr, ua.wr]) (by rw [sp', ue.sp, ud.sp, ub.sp, ua.sp])
      (fun r hr h30 => by
        obtain ⟨-, n1, n2, n3, n4, -⟩ := pres_ne r hr
        rw [cs' r hr h30, k r n1 n2 n3 n4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have hv := hp.v_nw
  have e := vl_mul hp
  have := v_le hi
  have := hp.pos
  rw [toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the parts of `scratch` and the stack we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (stkR s₀) :=
  hp.stk_v.symm.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub
  · exact vAt_stk hp hk

theorem call_kept {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w
    · exact keep_stk hp

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))
      (by rw [hl]; exact lt)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (8 * k)) 8 := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (8 * k)) 8
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem sh3 {s₀ : State} (hp : Pre s₀) :
    BitVec.ofNat 64 (128 * rr s₀) >>> 3 = BitVec.ofNat 64 (16 * rr s₀) := by
  rw [shr_ofNat _ (r_lt hp)]; exact congrArg (BitVec.ofNat _) (by omega)

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  unfold step2
  refine WP.seq (wp_mov fun a ua => wp_mov fun b ub => wp_lsr (by decide) fun d ud => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : d.rd = s₀.rd := by rw [ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : d.wr = s₀.wr := by rw [ud.wr, ub.wr, ua.wr, h.wr]
  have esp : d.sp = s₀.sp := by rw [ud.sp, ub.sp, ua.sp, h.sp]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀) (by omega)
    (by omega) (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.x19])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.x24])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.x22, sh3 hp])
    (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, -⟩ := pres_ne r hr
    rw [gt r h9 h10 h11 h12, ke r h9 h10 h11]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun f uf => ?_))
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (A := vAt s₀ i) (by rw [uf.gpr, kt _ (by decide), h.x24])
    (by rw [kf _ (by decide), h.x19]) (by rw [kf _ (by decide), h.x21])
    (by rw [kf _ (by decide), h.x22]) (by rw [uf.sp, spt, esp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((vAt_b hp hi).sub_right b_sub') ((vAt_s hp hi).sub_right w_sub) (vAt_stk hp hi).symm
    (vAt_nw hp hi) (InRegions.right (vAt_in hp hi)) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .x30 → s4.gpr r = s.gpr r := fun r hr h30 => by
    rw [cs4 r hr h30, kf r hr]
  refine wp_add fun s5 u5 => wp_subImm (by decide) fun s6 u6 => WP.block_nil ?_
  have k6 : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x23 → r ≠ .x24 → s6.gpr r = s.gpr r :=
    fun r hr h30 h1 h2 => by rw [u6.other _ h1, u5.other _ h2, k4 r hr h30]
  have e23 : s6.gpr .x23 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), k4 _ (by decide) (by decide), h.x23, dec_count hi]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [u6.sp, u5.sp, sp4, uf.sp, spt, esp],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x19],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x20],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x21],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x22], e23, ?_,
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by decide) (by decide), k4 _ (by decide) (by decide),
      h.x24, h.x22, vAt_succ]
  · rw [e23, dec_ne hi hN]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) (.nonzero .x .x23)) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (NN s₀ - i)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (NN s₀ - 1)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  unfold rmMid
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 184) (by decide) (by rw [h.x21])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_subImm (by decide) fun b ub => WP.block_nil ?_
  have ka : a.gpr .x23 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .x23 → r ≠ .x24 → b.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ub.other _ h2, ua.other _ h1]
  have hm : b.mem = s.mem := by rw [ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ub.rd, ua.rd, h.rd], by rw [ub.wr, ua.wr, h.wr],
    by rw [ub.sp, ua.sp, h.sp], by rw [k _ (by decide) (by decide), h.x19],
    by rw [k _ (by decide) (by decide), h.x20], by rw [k _ (by decide) (by decide), h.x21],
    by rw [k _ (by decide) (by decide), h.x22], by rw [ub.other _ (by decide), ka]; rfl, ?_,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk,
    ?_, ?_⟩
  · rw [ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bP s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (NN s₀ - 1) =
      BitVec.ofNat 64 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_lt (by have := jOf_lt hp m; omega), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem j_addr {s₀ : State} (hp : Pre s₀) :
    bP s₀ + BitVec.ofNat 64 (128 * rr s₀) - BitVec.ofNat 64 64 =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) :=
  add_sub64 _ (by have := hp.pos; omega)

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := hp.s_nw
  rw [hp.wr, add_ofNat]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem t_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem t_b {s₀ : State} (hp : Pre s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_nw {s₀ : State} (hp : Pre s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [toNat_add_ofNat _ (by omega)]
  omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) lt]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `x9 = j`. -/
theorem j_ok {s₀ : State} (hp : Pre s₀) {s : State} (h19 : s.gpr .x19 = bP s₀)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)) (h24 : s.gpr .x24 = BitVec.ofNat 64 (NN s₀ - 1))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block jBlock) s fun s' => Upd s s' .x9 (BitVec.ofNat 64 (jOf s₀ s.mem)) := by
  have lt := r_lt hp
  have := hp.pos
  unfold jBlock
  refine wp_add fun a ua => wp_subImm (by decide) fun b ub => ?_
  refine wp_ldr (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (by decide)
    (by rw [ub.gpr, ua.gpr, h19, h22, j_addr hp]; exact BitVec.add_zero _)
    (by rw [ub.rd, ub.wr, ua.rd, ua.wr, hrd, hwr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega)))
    fun d ud => wp_and fun e ue => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [ue.mem, ud.mem, ub.mem, ua.mem], by rw [ue.rd, ud.rd, ub.rd, ua.rd],
    by rw [ue.wr, ud.wr, ub.wr, ua.wr], by rw [ue.sp, ud.sp, ub.sp, ua.sp]⟩
  · rw [ue.gpr, ud.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h24,
      ub.mem, ua.mem, jOf_eq hp]
  · rw [ue.other _ hr, ud.other _ hr, ub.other _ hr, ua.other _ hr]

/-- The address of `V[j]`. -/
theorem vAt_madd (s₀ : State) (j : Nat) :
    vP s₀ + BitVec.ofNat 64 j * BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ j := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.x19 h.x22 h.x24 h.rd h.wr) fun a ua => ?_)
  refine WP.seq (wp_madd fun b ub => wp_mov fun d ud => wp_addImm (by decide) fun e ue =>
    wp_lsr (by decide) fun f uf => WP.block_nil ?_)
  have rdf : f.rd = s₀.rd := by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have wrf : f.wr = s₀.wr := by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have spf : f.sp = s₀.sp := by rw [uf.sp, ue.sp, ud.sp, ub.sp, ua.sp, h.sp]
  have mf : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, -⟩ := pres_ne r hr
    rw [uf.other _ h12, ue.other _ h11, ud.other _ h9, ub.other _ h10, ua.other _ h9]
  have h10 : f.gpr .x10 = vAt s₀ (jOf s₀ s.mem) := by
    rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), ub.gpr,
      ua.gpr, ua.other _ (by decide), ua.other _ (by decide), h.x20, h.x22, vAt_madd]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem)) (d := tP s₀)
    (n := 16 * rr s₀) (by omega) (by omega)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.x19])
    h10
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x22, sh3 hp])
    (fun k hk => by rw [rdf, wrf]; exact b_word hp hk)
    (fun k hk => by rw [rdf, wrf]; exact InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wrf]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [mf, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, h13, h14⟩ := pres_ne r hr
    rw [gt r h9 h10 h11 h12 h13 h14, kf r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_addImm (by decide) fun q1 v1 => ?_))
  have kq : ∀ r ∈ preserved, q1.gpr r = s.gpr r := fun r hr => by
    rw [v1.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (A := tP s₀) (by rw [v1.gpr, kt _ (by decide), h.x21])
    (by rw [kq _ (by decide), h.x19]) (by rw [kq _ (by decide), h.x21])
    (by rw [kq _ (by decide), h.x22]) (by rw [v1.sp, spt, spf])
    (by rw [v1.rd, rdt, rdf]) (by rw [v1.wr, wrt, wrf])
    (t_b hp) (t_w hp) (hp.stk_s.sub_right (t_sub hp)) (t_nw hp)
    (InRegions.right (t_in hp)) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .x30 → s4.gpr r = s.gpr r := fun r hr h30 => by
    rw [cs4 r hr h30, kq r hr]
  refine wp_subImm (by decide) fun s5 u5 => WP.block_nil ?_
  have k5 : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x23 → s5.gpr r = s.gpr r := fun r hr h30 h1 => by
    rw [u5.other _ h1, k4 r hr h30]
  have e23 : s5.gpr .x23 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u5.gpr, k4 _ (by decide) (by decide), h.x23, dec_count hi]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v1.rd, rdt, rdf], by rw [u5.wr, wr4, v1.wr, wrt, wrf],
    by rw [u5.sp, sp4, v1.sp, spt, spf],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x19],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x20],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x21],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x22], e23,
    by rw [k5 _ (by decide) (by decide) (by decide), h.x24],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [e23, dec_ne hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) (.nonzero .x .x23)) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) := by
  have hin : ∀ d, d + 8 ≤ 256 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]
    exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ rmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.kept.1
  simp only [rmEpilogue, rmSaved, List.map_cons, List.map_nil]
  refine wp_ldr (by decide) (by rw [h.x21]) (hin 128 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_ldr (by decide) (by rw [ua.other _ (by decide), h.x21])
    (hin 136 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_ldr (by decide) (by rw [ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 144 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_ldr (by decide) (by rw [uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (hin 152 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_ldr (by decide) (by rw [ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 160 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_ldr (by decide) (by rw [ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 168 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => ?_
  refine wp_ldr (by decide) (by rw [uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (hin 176 (by omega) _ (uf.rd.trans (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))))
      (uf.wr.trans (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))))
    fun g ug => WP.block_nil ?_
  have hm : g.mem = s.mem := by rw [ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, by rw [ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp], fun p hp' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      sv (.x19, 128) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.mem,
      sv (.x20, 136) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.mem, ua.mem, sv (.x22, 144) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem,
      ub.mem, ua.mem, sv (.x23, 152) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x24, 160) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x30, 168) (by simp [rmSaved])]
  · rw [ug.gpr, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.x21, 176) (by simp [rmSaved])]

/-! ## The whole function -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hsp hm => setup_ok hp g hrd hwr hsp hm

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧
      Proof.Scrypt.roMixAArch64.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₆.sp, ?_⟩
  show bytesAt s'.mem (bP s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
  rw [hm', ← h₆.x, Nat.sub_self]
  rfl

end VG.Proof.Scrypt.AArch64.RoMix

/-!
# scryptROMix on AArch64: verified

Untrusted: everything here is checked by Lean. `BlockMixSpec` of the
verified `vg_scrypt_blockmix`, from its `Verified` proof by `WP.callF`; then
constant time, up to the indices `j`, as on x86-64 (`X86_64/RoMixCT.lean`):
we relate two runs (`RelCT`). Correctness determines our registers from the
public arguments, so they agree between the calls, where the taint analysis
proves each piece constant time; the calls are constant time by
scryptBlockMix's own proof. In step 3, the address of `V[j]` depends on `j`,
which the contract declares public: the two runs compute the same `j`, since
both compute their indices in order (`Inv3.js`) and agree on the whole list.
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_lsr eval_nonzero)
open VG.Proof.Scrypt.AArch64.BlockMix (covers_of_in covers_pair)
open VG.Proof.Scrypt.Memory (InRegions.right)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem blockMix_fdepth : Impl.Scrypt.AArch64.blockMix.fdepth = 1 := by decide +kernel

theorem bm_pre {s : State} {src dst scr : Addr} {r : Nat} (h0 : s.gpr .x0 = src)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 r) (h2 : s.gpr .x2 = dst) (h3 : s.gpr .x3 = BitVec.ofNat 64 r)
    (h4 : s.gpr .x4 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩) (hsd : Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩) (hsp : 16 ≤ s.sp.toNat)
    (bsrc : (below s.sp 16).Disjoint ⟨src, 128 * r⟩) (bdst : (below s.sp 16).Disjoint ⟨dst, 128 * r⟩)
    (bscr : (below s.sp 16).Disjoint ⟨scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 64) (ndst : dst.toNat + 128 * r ≤ 2 ^ 64)
    (nscr : scr.toNat + 128 ≤ 2 ^ 64)
    (isrc : InRegions (s.rd ++ s.wr) src (128 * r)) (idst : InRegions s.wr dst (128 * r))
    (iscr : InRegions s.wr scr 128) :
    Proof.Scrypt.blockMixAArch64.pre
      (s.callEntry.withRegions [⟨src, 128 * r⟩] [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) ∧
    Covers ([⟨src, 128 * r⟩] ++ [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨dst, 128 * r⟩, ⟨scr, 128⟩] s.wr := by
  have tr : (BitVec.ofNat 64 r).toNat = r := toNat_ofNat_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have cw := covers_pair (covers_of_in idst) (covers_of_in iscr)
  refine ⟨?_, ?_, cw⟩
  · simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4, tr, c128]
    exact ⟨trivial, trivial, hds, hsd, hss, hsp, bsrc, bdst, bscr, nsrc, ndst, nscr, trivial, hr⟩
  · have h1 := covers_of_in isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.AArch64.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 h4 hr hlt hds hsd hss hsp bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  have tr : (BitVec.ofNat 64 r).toNat = r := toNat_ofNat_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := bm_pre h0 h1 h2 h3 h4 hr hlt hds hsd hss hsp bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr
  refine WP.callF (k := Proof.Scrypt.blockMixAArch64) BlockMix.blockMix_correct p c₁ c₂ ?_
    (by rw [blockMix_fdepth]; decide)
  intro s₂ hrd hwr hsp' hf hcs hpost
  simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2, tr] at hpost
  rw [blockMix_fdepth] at hf
  exact hQ s₂ hrd hwr hsp' hcs hf hpost

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.x1]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.x1, hq.x3]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.x1, hq.x2]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.x4]

end

/-- The registers the loops keep, with `x24 = bp` and `x23 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = q
  x24 : s.gpr .x24 = bp

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

theorem kRegs_ne : ∀ r ∈ kRegs, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x9 := by
  decide

theorem kRegs_pres : ∀ r ∈ kRegs, r ∈ preserved ∧ r ≠ .x30 ∧ r ∉ linkRegs := by decide

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r ∈ kRegs, s'.gpr r = s.gpr r) : KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hk _ (by decide)).trans h.x19,
    (hk _ (by decide)).trans h.x20, (hk _ (by decide)).trans h.x21, (hk _ (by decide)).trans h.x22,
    (hk _ (by decide)).trans h.x23, (hk _ (by decide)).trans h.x24⟩

/-- Whether an instruction writes none of `kRegs`. -/
def kFree (i : Instr) : Bool := kRegs.all fun r => dstOf i != some r

/-- `KR` survives code that writes none of its registers. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs kFree = true) {s₀ : State} {bp q : Addr}
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : KR s₀ bp q s) : KR s₀ bp q s' := by
  obtain ⟨rd, wr, sp⟩ := Exec.rdwr he
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine h.keep rd wr sp fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (kRegs_pres r hr).2.2)
  have := hc i hi
  simp only [kFree, List.all_eq_true, bne_iff_ne, ne_eq] at this
  exact this r hr

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

/-- The registers `KR` fixes, and the stack pointer, agree in two runs. -/
theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs (extra ++ kRegs)) s s' := by
  refine agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, bP, bP, hq.x0]
  · rw [h.x20, h'.x20, vP, vP, hq.x2]
  · rw [h.x21, h'.x21, sc, sc, hq.x4]
  · rw [h.x22, h'.x22, hq.rr]
  · rw [h.x23, h'.x23, hq']
  · rw [h.x24, h'.x24, hbp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  x0 : s.gpr .x0 = A
  x1 : s.gpr .x1 = BitVec.ofNat 64 (rr s₀)
  x2 : s.gpr .x2 = bP s₀
  x3 : s.gpr .x3 = BitVec.ofNat 64 (rr s₀)
  x4 : s.gpr .x4 = sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_v {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt s₀ i) :=
  ⟨(vAt_b hp hi).sub_right b_sub', (vAt_s hp hi).sub_right w_sub, (vAt_stk hp hi).symm,
    vAt_nw hp hi, InRegions.right (vAt_in hp hi)⟩

theorem srcOK_t {s₀ : State} (hp : Pre s₀) : SrcOK s₀ (tP s₀) :=
  ⟨t_b hp, t_w hp, hp.stk_s.sub_right (t_sub hp), t_nw hp, InRegions.right (t_in hp)⟩

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixAArch64.pre (s.callEntry.withRegions [⟨A, 128 * rr s₀⟩]
      [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * rr s₀⟩] ++ [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  exact bm_pre ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.sp]; exact hp.sp16) (by rw [h.sp]; exact hA.stk)
    (by rw [h.sp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.sp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.AArch64.blockMix) s (KR s₀ bp q) := by
  have lt := r_lt hp
  exact blockMixSpec s A (bP s₀) (sc s₀) (rr s₀) ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.sp]; exact hp.sp16) (by rw [h.sp]; exact hA.stk)
    (by rw [h.sp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.sp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp) _ fun _ rd wr sp cs _ _ =>
      h.keep rd wr sp fun r hr => cs r (kRegs_pres r hr).1 (kRegs_pres r hr).2.1

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {A A' : Addr}
    (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.AArch64.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.x0.symm
  have es : sc s₀' = sc s₀ := hq.x4.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_correct BlockMix.blockMix_ct [⟨A, 128 * rr s₀⟩]
    [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [Proof.Scrypt.blockMixAArch64, State.withRegions_gpr, State.withRegions_sp,
        State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3, ha.x4,
        ha'.x0, ha'.x1, ha'.x2, ha'.x3, ha'.x4, eb, es, er, h.sp, h'.sp, hq.sp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## Relating pieces of code -/

/-- Code that writes none of `kRegs` keeps `KR` in both runs. -/
theorem RelCT.keepK {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hc : c.allInstrs kFree = true) {s₀ s₀' : State} {bp q bp' q' : Addr}
    (hk : ∀ s s', P s s' → KR s₀ bp q s ∧ KR s₀' bp' q' s') :
    RelCT isa P c fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' :=
  fun _ _ _ _ _ _ hp e e' =>
    ⟨(h _ _ _ _ _ _ hp e e').1, KR.exec hc e (hk _ _ hp).1, KR.exec hc e' (hk _ _ hp).2⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Setting up the calls -/

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : Addr} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .x0 = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_lsr (by decide) fun a ua => wp_mov fun b ub => wp_mov fun d ud => wp_mov fun e ue =>
    WP.block_nil ⟨?_, ?_⟩
  · exact h.keep (by rw [ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [ue.wr, ud.wr, ub.wr, ua.wr])
      (by rw [ue.sp, ud.sp, ub.sp, ua.sp]) fun r hr => by
        obtain ⟨-, h1, h2, h3, h4, -⟩ := kRegs_ne r hr
        rw [ue.other _ h4, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .x1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h.x22, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  exact ⟨by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hA],
    by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), h1],
    by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.x19],
    by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), h1],
    by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x21]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([mov .x0 .x24] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.x24])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.addImm .x .x0 .x21 192] : List Instr) ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_addImm (by decide) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.x21])

/-! ## Step 2, in two runs -/

theorem eval_x23 (s : State) : isa.eval (.nonzero .x .x23) s = some (s.gpr .x23 != 0) :=
  eval_nonzero s .x23

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv2 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt s₀ i = vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (vAt t₀ i) (BitVec.ofNat 64 (NN t₀ - i)) t
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block [mov .x9 .x19, mov .x10 .x24, .lsr .x .x11 .x22 3]) copyLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide))
      (by decide +kernel) fun _ _ h => ⟨h.1.kr, h.2.kr⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([mov .x0 .x24] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (vAt s₀ i) s) ∧ (K s₀' s' ∧ Args s₀' (vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt s₀ i) (q := BitVec.ofNat 64 (NN s₀ - i)) (bp' := vAt s₀' i)
    (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block [.add .x .x24 .x24 .x22, .subImm .x .x23 .x23 1]) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := RelCT.assoc (ac.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.AArch64.blockMix) (.nonzero .x .x23))
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.AArch64.blockMix)
    (c := .nonzero .x .x23) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_x23, eval_x23, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3 -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j :=
  WP.mono (j_ok hp h.x19 h.x22 h.x24 h.rd h.wr) fun _ u =>
    ⟨h.keep u.rd u.wr u.sp fun r hr => u.other r (kRegs_ne r hr).2.2.2.2.2, by rw [u.gpr, hj]⟩

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop :=
    KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .x9 = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .x9 = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .x9 = BitVec.ofNat 64 j))
      (.seq (.block [.madd .x .x10 .x9 .x22 .x20, mov .x9 .x19, .addImm .x .x11 .x21 192,
        .lsr .x .x12 .x22 3]) xorLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([.x9] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide))
      (by decide +kernel) fun _ _ h => ⟨h.1.1, h.2.1⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.addImm .x .x0 .x21 192] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.subImm .x .x23 .x23 1])
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (RelCT.assoc (mx.seq ((x.seq cl).seq e)))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.AArch64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.AArch64.blockMix) (.nonzero .x .x23))
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.AArch64.blockMix)
    (c := .nonzero .x .x23) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_x23, eval_x23, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.AArch64.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.AArch64.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => by
        rw [e, e']
        refine agree_of hq.sp fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x9, .x10, .x11])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.x9, h'.x9, hq.rr]
        · rw [h.x10, h'.x10]
        · rw [h.x11, h'.x11, RoMix.vl, RoMix.vl, hq.x3]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x10, .x20, .x21])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.x10, h'.x10, hq.NN]
        · rw [h.x20, h'.x20, vP, vP, hq.x2]
        · rw [h.x21, h'.x21, sc, sc, hq.x4]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x21])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.x21, h'.x21, sc, sc, hq.x4]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [.x21])
      (fun _ _ h => agree_of (by rw [h.1.sp, h.2.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.x21, h.2.x21, sc, sc, hq.x4]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixAArch64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- No instruction of ROMix, or of the functions it calls, writes `x25`–`x29`. -/
theorem others_kept :
    (instrs Impl.Scrypt.AArch64.roMix).all
      (fun i => [Reg.x25, .x26, .x27, .x28].all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem preserved_cases :
    ∀ r ∈ preserved, r ∈ rmSaved.map Prod.fst ∨ r ∈ [Reg.x25, .x26, .x27, .x28] := by
  decide

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x5 => 3 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixAArch64.post s s' := by
  obtain ⟨t, s', he, hk, hsp, hpost⟩ := correct blockMixSpec (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, hpost⟩
  rcases preserved_cases r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hk p hp
  · have hc := others_kept
    rw [List.all_eq_true] at hc
    refine Exec.gpr (fun i hi => ?_) he (.inr (by revert h; revert r; decide))
    have := hc i hi
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this r h

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixAArch64.pre Proof.Scrypt.roMixAArch64.pub
    Impl.Scrypt.AArch64.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.roMix (Spec.Scrypt.roMixContract AArch64.abi 16) :=
  Verified.of_correct roMix_correct roMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.RoMix.satState]
          [Proof.Scrypt.AArch64.RoMix.satState] using Proof.Scrypt.AArch64.RoMix.satState }

end VG.Proof.Scrypt.AArch64.RoMix
