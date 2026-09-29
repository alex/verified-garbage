import VerifiedGarbage.Proof.Scrypt.AArch64.Common
import VerifiedGarbage.Proof.Scrypt.AArch64.Contract
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix

/-!
# scryptROMix on AArch64: the precondition

Untrusted: everything here is checked by Lean. The regions the function
works on, and `BlockMixSpec`: what a call of `vg_scrypt_blockmix` does (the
verified one meets it: `Proof/Scrypt/AArch64/RoMixCT.lean`).
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Scrypt.X86_64.BlockMix (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  disj_off InRegions.of_mem)

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
