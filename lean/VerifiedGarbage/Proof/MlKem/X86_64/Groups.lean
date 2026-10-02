import VerifiedGarbage.Impl.MlKem.X86_64.Compress
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on x86-64: segments of groups of values and their bytes

The pieces of the compressions (`vg_mlkem_compress_encode`,
`vg_mlkem1024_compress_encode`, …) that move a segment of a group between
values and bytes, for any width `d ≤ 11`: values `o, …, o + c - 1` of the
group accumulated in `r10` from the last (`ceAcc_ok`, the number whose
base-`2ᵈ` digits they are), bytes stored from `r10` (`ceSt_ok`); bytes `o, …,
o + b - 1` loaded into `r10` from the last (`ddLd_ok`, the number whose bytes
they are), and values taken from the bottom of `r10` (`ddVals_ok`). A segment
is a chunk of the number of the group (`chunk_eq`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## Chunks of a number -/

/-- Bits `s + p … s + p + m - 1` of the number whose digits are `c` digits
of `L` from digit `o`: those of the number of `L` from bit `w·o + s + p`. -/
theorem chunk_eq {w : Nat} {L : List Nat} (hL : ∀ a ∈ L, a < 2 ^ w) (o c s p m : Nat) (hp : s + p + m ≤ w * c) :
    digits w ((L.drop o).take c) / 2 ^ s / 2 ^ p % 2 ^ m = digits w L / 2 ^ (w * o + s + p) % 2 ^ m := by
  have hd := digits_div hL o
  have hm := digits_mod (L := L.drop o) (fun a ha => hL a (List.mem_of_mem_drop ha)) c
  rw [← hm, Nat.div_div_eq_div_mul, ← Nat.pow_add, mod_pow_div_mod _ (show s + p + m ≤ w * c by omega), ← hd,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_assoc]

/-! ## Bytes written in two parts -/

theorem off_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem Written.append {m m₁ m₂ : Mem} {o : Addr} {a c : Nat} {v₁ v₂ : Nat → Byte} (h₁ : Written m m₁ o a v₁)
    (h₂ : Written m₁ m₂ (o + BitVec.ofNat 64 a) c v₂) (hac : a + c < 2 ^ 64) :
    Written m m₂ o (a + c) fun j => if j < a then v₁ j else v₂ (j - a) := by
  intro x
  rw [h₂ x, h₁ x]
  have e : (x - (o + BitVec.ofNat 64 a)) = (x - o) - BitVec.ofNat 64 a := by bv_omega
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  generalize x - o = y at e ⊢
  rw [e]
  by_cases hx : y.toNat < a
  · have : ¬ (y - BitVec.ofNat 64 a).toNat < c := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA]
      rw [show 2 ^ 64 - a + y.toNat = 2 ^ 64 - (a - y.toNat) by omega, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ifn this, ifp hx, ifp (show y.toNat < a + c by omega)]
    dsimp only
    rw [ifp hx]
  · have e2 : (y - BitVec.ofNat 64 a).toNat = y.toNat - a := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA, show 2 ^ 64 - a + y.toNat = 2 ^ 64 + (y.toNat - a) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
    rw [e2, ifn hx]
    by_cases hc : y.toNat - a < c
    · rw [ifp hc, ifp (show y.toNat < a + c by omega)]
      dsimp only
      rw [ifn hx]
    · rw [ifn hc, ifn (by omega)]

/-! ## Compressing -/

theorem r10zero_ok (s : State) :
    WP isa (.block [.mov32 .r10 (.imm 0)]) s fun s' => (s'.gpr .r10 = 0 ∧ s'.mem = s.mem) ∧
      Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- `Compress_d` of `a`, as the code computes it with the multiplier `M` and
the rounding constant `r`. -/
def ceV (r d : Nat) (a : BitVec 32) (M : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) +
    BitVec.ofNat 64 r) >>> 19) &&& BitVec.ofNat 32 (2 ^ d - 1))

theorem ceV_toNat {r d : Nat} (hd : d ≤ 11) {a : BitVec 32} {M : BitVec 64}
    (h : a.toNat * M.toNat + r < 2 ^ 30) :
    (ceV r d a M).toNat = (a.toNat * M.toNat + r) / 2 ^ 19 % 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat)).toNat = a.toNat * M.toNat := by
    rw [BitVec.toNat_ofNat, toNat_setWidth64, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r).toNat =
      a.toNat * M.toNat + r := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := r) (by omega)]; omega
  have h3 : ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r) >>> 19).toNat =
      (a.toNat * M.toNat + r) / 2 ^ 19 := by rw [shr_toNat, h2]
  rw [ceV, toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    toNat_setWidth32_64 (by rw [h3]; omega), h3]

theorem ceCoef_ok (r d j : Nat) (hr : r < 2 ^ 31) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ceCoef r d j)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight (64 - d) +
          ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceCoef
  xrun [hin, show 1 ≤ 64 - d by omega, show 64 - d ≤ 63 by omega, ceV, sx_ofNat hr]

theorem digits_range_succ (d : Nat) (V : Nat → Nat) (t : Nat) :
    digits d ((List.range (t + 1)).map V) = V 0 + 2 ^ d * digits d ((List.range t).map fun u => V (u + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, digits_cons, List.map_map]
  rfl

theorem digits_map_lt {d : Nat} {V : Nat → Nat} {t : Nat} (h : ∀ u < t, V u < 2 ^ d) :
    digits d ((List.range t).map V) < 2 ^ (d * t) := by
  have := digits_lt (w := d) (L := (List.range t).map V) (by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact h u (List.mem_range.mp hu))
  simpa using this

/-- The `c` compressed values `o, …, o + c - 1` of a group, from the last, into `r10`. -/
theorem ceAcc_ok {r d o c : Nat} (hrr : r < 2 ^ 31) (hd1 : 1 ≤ d) (hd : d ≤ 11) (hdc : d * c ≤ 60) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * (o + j))) 4) (V : Nat → Nat)
    (hV : ∀ j < c, (ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * (o + j))) 32) (s.gpr .r9)).toNat = V j)
    (hVlt : ∀ j < c, V j < 2 ^ d) :
    WP isa (.block (ceAcc r d o c)) s fun s' =>
      (s'.gpr .r10).toNat = digits d ((List.range c).map V) ∧ s'.mem = s.mem ∧
        Keep [.rax, .rdx, .r10] s s' := by
  unfold ceAcc
  rw [WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  have h90 : s₀.gpr .r9 = s.gpr .r9 := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .rdx, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits d ((List.range t).map fun u => V (c - t + u)))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) c (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  have h9 : s'.gpr .r9 = s.gpr .r9 := by rw [hk.gpr (by decide), h90]
  refine WP.mono (ceCoef_ok r d (o + (c - 1 - t)) hrr hd1 hd s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hdt : d * t + d ≤ 60 := by
    have := Nat.mul_le_mul_left d (show t + 1 ≤ c by omega); rw [Nat.mul_succ] at this; omega
  have hacc : digits d ((List.range t).map fun u => V (c - t + u)) < 2 ^ (d * t) :=
    digits_map_lt fun u hu => hVlt _ (by omega)
  have hlt : 2 ^ (d * t) * 2 ^ d ≤ 2 ^ 60 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hdt
  have hv := hVlt (c - 1 - t) (by omega)
  have hA : digits d ((List.range t).map fun u => V (c - t + u)) * 2 ^ d < 2 ^ 60 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hacc (Nat.two_pow_pos d)) hlt
  have hpd : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  rw [h10, BitVec.toNat_add, rotr_toNat _ (by omega) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))),
    hr, hdi, hm, h9, hV _ (by omega), digits_range_succ, show 64 - (64 - d) = d by omega,
    show c - (t + 1) + 0 = c - 1 - t by omega]
  have e : (fun u => V (c - (t + 1) + (u + 1))) = fun u => V (c - t + u) := by
    funext u; congr 1; omega
  rw [e, Nat.mod_eq_of_lt (by omega), Nat.add_comm, Nat.mul_comm]

theorem ceStore_ok (k : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1) :
    WP isa (.block (ceStore k)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 k) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceStore
  xrun [hout]

/-- The `nb` low bytes of `r10` stored at `r8 + k0`. -/
theorem ceSt_ok {k0 nb : Nat} (hb : nb ≤ 8) (s : State)
    (hout : ∀ k < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 (k0 + k)) 1) :
    WP isa (.block (ceSt k0 nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) nb
          (fun k => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * k))) ∧
        Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = (s.gpr .r10).toNat / 2 ^ (8 * k) ∧
    Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) k (fun t => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * t))))
    (fun k s' hk ⟨hkp, hr, hw⟩ => ?_) nb (Nat.le_refl _) s ⟨Keep.refl _ _, by simp, Written.nil _ _ _⟩)
    fun s' ⟨hkp, _, hw⟩ => ⟨hw, hkp⟩
  have h8 : s'.gpr .r8 = s.gpr .r8 := hkp.gpr (by decide)
  refine WP.mono (ceStore_ok (k0 + k) s' (by rw [hkp.2.2, h8]; exact hout k hk))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8, ← off_add']
    refine (hw.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k
    · subst e; rw [ifp rfl, b8_eq64, hr]
    · rw [ifn e]

/-! ## Decompressing -/

theorem ddByte_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (ddByte k)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight 56 + BitVec.setWidth 64 (s.mem (s.gpr .rdi + BitVec.ofNat 64 k)) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddByte
  xrun [hin]

/-- Bytes `o, …, o + b - 1` of a group, from the last, into `r10`. -/
theorem ddLd_ok {o b : Nat} (hb : b ≤ 7) (s : State)
    (hin : ∀ k < b, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (o + k)) 1) :
    WP isa (.block (ddLd o b)) s fun s' =>
      (s'.gpr .r10).toNat = digits 8 ((List.range b).map fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + k))).toNat) ∧
        s'.mem = s.mem ∧ Keep [.rax, .r10] s s' := by
  unfold ddLd
  rw [WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) b (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  refine WP.mono (ddByte_ok (o + (b - 1 - t)) s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hacc : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) < 2 ^ (8 * t) :=
    digits_map_lt fun u _ => BitVec.isLt _
  have hv := (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - 1 - t)))).isLt
  rw [h10, BitVec.toNat_add, rotr_toNat _ (by decide) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))), hr, hdi, hm,
    toNat_setWidth64_8, digits_range_succ, show 64 - 56 = 8 by rfl, show b - (t + 1) + 0 = b - 1 - t by omega]
  have e : (fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - (t + 1) + (u + 1))))).toNat) =
      fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat := by
    funext u; rw [show b - (t + 1) + (u + 1) = b - t + u by omega]
  have hA : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) * 2 ^ 8 < 2 ^ 56 := by
    have := Nat.mul_lt_mul_of_pos_right hacc (show 0 < 2 ^ 8 by decide)
    have h' : 2 ^ (8 * t) * 2 ^ 8 ≤ 2 ^ 56 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [e]
  have h64 : digits 8 ((List.range t).map fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) *
      2 ^ 8 + (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - 1 - t)))).toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hA (Nat.le_of_lt_succ hv)) (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.add_comm, Nat.mul_comm]

/-- The word `ddCoef` stores, from the accumulator `a`, with `q` in `r9`. -/
def ddW (d : Nat) (a M : BitVec 64) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&&
    BitVec.ofNat 32 (2 ^ d - 1))).toNat * M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))) >>> d)

theorem ddW_toNat {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 11) (a : BitVec 64) {M : BitVec 64} (hM : M.toNat = 3329) :
    (ddW d a M).toNat = (3329 * (a.toNat % 2 ^ d) + 2 ^ (d - 1)) / 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hp' : 2 ^ (d - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hy : (BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat = a.toNat % 2 ^ d := by
    rw [toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hyl : a.toNat % 2 ^ d < 2 ^ 11 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) hp
  generalize a.toNat % 2 ^ d = y at hy hyl ⊢
  have e1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat)).toNat = 3329 * y := by
    rw [BitVec.toNat_ofNat, hy, hM, Nat.mod_eq_of_lt (by omega)]; omega
  have e2 : (BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 2 ^ (d - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 3329 * y + 2 ^ (d - 1) := by
    rw [BitVec.toNat_add, e1, e2, Nat.mod_eq_of_lt (by omega)]
  have h3 : (3329 * y + 2 ^ (d - 1)) / 2 ^ d < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [ddW, toNat_setWidth32_64 (by rw [shr_toNat, h2]; exact h3), shr_toNat, h2]

theorem ddCoef_ok (d j : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ddCoef d j)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (ddW d (s.gpr .r10) (s.gpr .r9)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> d) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddCoef
  xrun [hout, show 1 ≤ d by omega, show d ≤ 63 by omega, ddW,
    sx_ofNat (show 2 ^ (d - 1) < 2 ^ 31 from Nat.pow_lt_pow_right (by decide) (by omega))]

/-- The low `c` values of `r10`, decompressed, to `rsi + 4o`, …. -/
theorem ddVals_ok {d o c : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 11) (hc : c ≤ 8) (s : State)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 4) :
    WP isa (.block (ddVals d o c)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 32 =
        ddW d (s.gpr .r10 >>> (d * j)) (s.gpr .r9)) ∧
      Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .rdx, .r10] s s' ∧
    s'.gpr .r10 = s.gpr .r10 >>> (d * j) ∧ Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧
    ∀ t < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + t))) 32 = ddW d (s.gpr .r10 >>> (d * t)) (s.gpr .r9))
    (fun j s' hj ⟨hk, hr, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, by simp, Frame.refl _ _, fun _ h => absurd h (by omega)⟩)
    fun s' ⟨hk, _, hf, hw⟩ => ⟨hw, hf, hk⟩
  have hsi : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk.gpr (by decide)
  refine WP.mono (ddCoef_ok d (o + j) hd1 hd s' (by rw [hk.2.2, hsi]; exact hout j hj))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, ?_, fun t ht => ?_⟩
  · rw [h10, hr, ← BitVec.shiftRight_add, Nat.mul_succ]
  · rw [hm, hsi, Nat.mul_add, ← off_add']
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
  · rw [hm, hsi, hr, h9]
    by_cases e : t = j
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_sep ?_ (by decide), hw t (by omega)]
      intro x h₁ h₂
      simp only [Nat.reduceDiv] at h₁ h₂
      have : t < j ∨ j < t := by omega
      rcases this with h | h <;> bv_omega

end VG.Proof.MlKem.X86_64
