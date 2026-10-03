import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.NormNum

/-!
# Multiword arithmetic on x86-64: the rounds of a Montgomery multiplication

`zeroAccLoop` clears the accumulator (`w + 2` words at `r8`); `round`
(for `i = r13`) adds `a_i B` and reduces (`round_ok`); `rounds` runs it for
`i = 0, …, w - 1`, keeping the accumulator `T < 2m` and
`T 2^(64 i) ≡ (a mod 2^(64 i)) B (mod m)` (`rounds_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum (round_lt round_mod round_sum_lt)

/-! ## Clearing the accumulator -/

structure ZeroInv (s : State) (B : Addr) (Z eA : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r14] s t
  rax : t.gpr .rax = 0
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s.mem t.mem
  val : wv t.mem B eA j = 0

theorem zeroAccLoop_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) :
    WP isa zeroAccLoop s fun t => wv t.mem B eA (w + 2) = 0 ∧ Outside B eA (8 * (w + 2)) s.mem t.mem ∧
      Keep [.rax, .r14] s t := by
  have hn := hs.nowrap
  unfold zeroAccLoop
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      ZeroInv s B Z eA 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), (k₁.trans k).mono (by decide),
      (k.gpr (by decide)).trans hax, h14, by rw [hm, hm₁]; exact Outside.refl _ _ _ _, rfl⟩
  have hstep : ∀ j, 0 ≤ j → j < w → ∀ t, ZeroInv s B Z eA j t →
      WP isa (.block ([.store (ix .r8 .r14) .rax] ++ [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) t
        fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ZeroInv s B Z eA (j + 1) t' := by
    intro j _ hj t hI
    have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
    have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (0 : BitVec 64))
      (by xrun [State.ea, ix, addr0 t8 hI.r14, hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega), hI.rax]) rfl)
      fun t₁ ⟨hm, k₁⟩ => ?_
    have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
    have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
    refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
    refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
      (k'.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.rax), h14, ?_, ?_⟩
    · rw [hm', hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x (by omega)
    · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
      rfl
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (ZeroInv s B Z eA) h0 hstep)
    fun t hI => ?_)
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = (t.mem.writeW (off B (eA + 8 * w)) (0 : BitVec 64)).writeW
      (off B (eA + 8 * w + 8)) (0 : BitVec 64))
    (by xrun [State.ea, ix, addr0 t8 t12, addr8 t8 t12, hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hI.rax]) rfl) fun t' ⟨hm, k'⟩ => ?_
  refine ⟨?_, ?_, (hI.keep.trans k').mono (by decide)⟩
  · rw [hm, show w + 2 = w + 1 + 1 from rfl, show eA + 8 * w + 8 = eA + 8 * (w + 1) by omega,
      wv_writeW_top _ _ _ _ _ (by omega), wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    rfl
  · rw [hm]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega)]
    exact hI.out x (by omega)

/-! ## A round -/

/-- Round `i` (`r13`): `rcx := a_i`, `T += a_i B`, `T := (T + u m) / 2⁶⁴`. -/
theorem round_ok {s : State} {B : Addr} {Z w eA eb eN ea i : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h9 : s.gpr .r9 = off B eb) (h10 : s.gpr .r10 = off B eN)
    (h11 : s.gpr .r11 = off B ea) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hi : i < w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (hT : wv s.mem B eA (w + 2) < 2 * wv s.mem B eN w) (hB : wv s.mem B eb w < wv s.mem B eN w) :
    WP isa round s fun t =>
      (∃ u < 2 ^ 64, 2 ^ 64 * wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) +
        (word s.mem B (ea + 8 * i)).toNat * wv s.mem B eb w + u * wv s.mem B eN w) ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have hNw : wv s.mem B eN w < 2 ^ (64 * w) := wv_lt _ _ _ _
  unfold round
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = word s.mem B (ea + 8 * i) ∧ t.mem = s.mem)
    (by xrun [State.ea, ix, addr0 h11 h13, hs.ld (show ea + 8 * i + 8 ≤ Z by omega)]) rfl)
    fun s₁ ⟨⟨hcx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hai := (word s.mem B (ea + 8 * i)).isLt
  have hbB : (word s.mem B (ea + 8 * i)).toNat * wv s.mem B eb w ≤ (2 ^ 64 - 1) * wv s.mem B eN w :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)
    ((k₁.gpr (by decide)).trans h12) (by omega) hw' hA hb sb (by
      rw [hm₁, hcx]
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this, Nat.sub_mul, Nat.one_mul] at *
      omega)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hcx] at hv₂
  rw [hm₁] at ho₂
  have hNeq : wv s₂.mem B eN w = wv s.mem B eN w := ho₂.wv (by omega) (by omega)
  have hN0 : word s₂.mem B eN = word s.mem B eN := ho₂.word (by omega) (by omega)
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := (k₁.trans k₂)
  refine WP.mono (reduceRow_ok hs₂ ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h10)
    ((k12.gpr (by decide)).trans h12) hw hw' hA hN sN (by
      rw [hN0, (k12.gpr (by decide) : s₂.gpr .r15 = s.gpr .r15)]; exact hinv) (by
      intro u hu
      rw [hv₂, hNeq]
      have hu' : u * wv s.mem B eN w ≤ (2 ^ 64 - 1) * wv s.mem B eN w := Nat.mul_le_mul_right _ (by omega)
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this]
      rw [Nat.sub_mul, Nat.one_mul] at hbB hu'
      have : 4 * 2 ^ (64 * w) ≤ 2 ^ 128 * 2 ^ (64 * w) - 2 ^ 66 * 2 ^ (64 * w) := by
        rw [← Nat.sub_mul]; exact Nat.mul_le_mul_right _ (by norm_num)
      omega)) fun t ⟨hv, ho, k₃⟩ => ?_
  refine ⟨⟨(word s₂.mem B eA).toNat * (s₂.gpr .r15).toNat % 2 ^ 64, Nat.mod_lt _ (by norm_num), ?_⟩,
    ho₂.trans ho, (k12.trans k₃).mono (by decide)⟩
  rw [hv, hv₂, hNeq]

/-! ## The rounds -/

/-- After rounds `0, …, i - 1` from `s₀`: the accumulator `T < 2m` and
`2^(64 i) T ≡ (a mod 2^(64 i)) B (mod m)`. -/
structure RoundsInv (s₀ : State) (B : Addr) (Z w eA eb eN ea : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rcx, .rdx, .rbp, .r14, .r13] s₀ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  out : Outside B eA (8 * (w + 2)) s₀.mem t.mem
  lt : wv t.mem B eA (w + 2) < 2 * wv s₀.mem B eN w
  cong : 2 ^ (64 * i) * wv t.mem B eA (w + 2) % wv s₀.mem B eN w =
    wv s₀.mem B ea i * wv s₀.mem B eb w % wv s₀.mem B eN w

theorem rounds_ok {s : State} {B : Addr} {Z w eA eb eN ea : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h9 : s.gpr .r9 = off B eb) (h10 : s.gpr .r10 = off B eN)
    (h11 : s.gpr .r11 = off B ea) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (h0 : wv s.mem B eA (w + 2) = 0) (hB : wv s.mem B eb w < wv s.mem B eN w) :
    WP isa rounds s (RoundsInv s B Z w eA eb eN ea w) := by
  have hn := hs.nowrap
  have hN0 : 0 < wv s.mem B eN w := by omega
  unfold rounds
  refine WP.seq (WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨h13, hm₁⟩, k₁⟩ => ?_)
  refine wp_upto (a := 0) (N := w) (by omega) (RoundsInv s B Z w eA eb eN ea) ?_ (fun _ h => h)
    ⟨hs.congr k₁.2.2, k₁.mono (by decide), h13, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hm₁, h0]; omega, by rw [hm₁, h0]; simp [wv]⟩
  intro i _ hi t hI
  have hk := hI.keep
  have frame : ∀ {d k}, d + 8 * k ≤ Z → (d + 8 * k ≤ eA ∨ eA + 8 * (w + 2) ≤ d) →
      wv t.mem B d k = wv s.mem B d k := fun h1 h2 => hI.out.wv h2 (by omega)
  refine WP.seq (WP.mono (round_ok hI.scr ((hk.gpr (by decide)).trans h8) ((hk.gpr (by decide)).trans h9)
    ((hk.gpr (by decide)).trans h10) ((hk.gpr (by decide)).trans h11) ((hk.gpr (by decide)).trans h12)
    hI.r13 hi hw hw' hA hb hN ha sb sN sa (by
      rw [hI.out.word (by omega) (by omega), (hk.gpr (by decide) : t.gpr .r15 = s.gpr .r15)]; exact hinv)
    (by rw [frame hN (by omega)]; exact hI.lt) (by rw [frame hb (by omega), frame hN (by omega)]; exact hB))
    fun t₁ ⟨⟨u, hu, hv⟩, ho, k₁'⟩ => ?_)
  have t₁13 : t₁.gpr .r13 = BitVec.ofNat 64 i := (k₁'.gpr (by decide)).trans hI.r13
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁'.gpr (by decide)).trans ((hk.gpr (by decide)).trans h12)
  refine WP.mono (count13_ok t₁ t₁13 t₁12 (by omega) (by omega)) fun t' ⟨hz, h13', hm', k'⟩ => ⟨hz, ?_⟩
  rw [frame hN (by omega), frame hb (by omega)] at hv
  have hai : (word t.mem B (ea + 8 * i)).toNat = (word s.mem B (ea + 8 * i)).toNat := by
    rw [hI.out.word (by omega) (by omega)]
  rw [hai] at hv
  refine ⟨hI.scr.congr (k'.2.2.trans k₁'.2.2), ((hk.trans k₁').trans k').mono (by decide), h13',
    by rw [hm']; exact hI.out.trans ho, ?_, ?_⟩
  · rw [hm']
    exact VG.Proof.Bignum.round_lt hv hI.lt (word s.mem B (ea + 8 * i)).isLt hB hu
  · rw [hm', show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add,
      VG.Proof.Bignum.round_step hv hI.cong]
    congr 1

end VG.Proof.Bignum.X86_64
