import VerifiedGarbage.Impl.MlKem.X86_64.Compress
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on x86-64: groups of values and their bytes

The pieces of `compressEncode` and `decodeDecompress` that move a group
between values and bytes, for any width `d`, group of `c` values and `b`
bytes: the values accumulated in `r10` from the last (`ceCoefs_ok`, the number
whose base-`2ᵈ` digits they are), stored as bytes (`ceStores_ok`); bytes
loaded from the last (`ddBytes_ok`, the number whose bytes they are), and
values taken from the bottom (`ddCoefs_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem sx262080 : BitVec.signExtend 64 (262080 : BitVec 32) = 262080 := by decide

/-- `Compress_d` of `a`, as the code computes it with the multiplier `M`. -/
def ceV (d : Nat) (a : BitVec 32) (M : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) +
    262080) >>> 19) &&& BitVec.ofNat 32 (2 ^ d - 1))

theorem ceV_toNat {d : Nat} (hd : d ≤ 10) {a : BitVec 32} {M : BitVec 64}
    (h : a.toNat * M.toNat + 262080 < 2 ^ 30) :
    (ceV d a M).toNat = (a.toNat * M.toNat + 262080) / 2 ^ 19 % 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hd
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat)).toNat = a.toNat * M.toNat := by
    rw [BitVec.toNat_ofNat, toNat_setWidth64, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + 262080).toNat =
      a.toNat * M.toNat + 262080 := by
    rw [BitVec.toNat_add, h1, show (262080 : BitVec 64).toNat = 262080 from rfl]; omega
  have h3 : ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + 262080) >>> 19).toNat =
      (a.toNat * M.toNat + 262080) / 2 ^ 19 := by rw [shr_toNat, h2]
  rw [ceV, toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    toNat_setWidth32_64 (by rw [h3]; omega), h3]

theorem ceCoef_ok (d j : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 10) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ceCoef d j)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight (64 - d) +
          ceV d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceCoef
  xrun [hin, show 1 ≤ 64 - d by omega, show 64 - d ≤ 63 by omega, ceV, sx262080]

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

/-- The `c` compressed values of a group, from the last, into `r10`. -/
theorem ceCoefs_ok {d c : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 10) (hdc : d * c ≤ 40) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (h0 : s.gpr .r10 = 0) (V : Nat → Nat)
    (hV : ∀ j < c, (ceV d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9)).toNat = V j)
    (hVlt : ∀ j < c, V j < 2 ^ d) :
    WP isa (.block ((List.range c).flatMap fun t => ceCoef d (c - 1 - t))) s fun s' =>
      (s'.gpr .r10).toNat = digits d ((List.range c).map V) ∧ s'.mem = s.mem ∧
        Keep [.rax, .rdx, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .rdx, .r10] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits d ((List.range t).map fun u => V (c - t + u)))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) c (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, hk⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := hk.gpr (by decide)
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk.gpr (by decide)
  refine WP.mono (ceCoef_ok d (c - 1 - t) hd1 hd s' (by rw [hk.2.1, hk.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hdt : d * t + d ≤ 40 := by
    have := Nat.mul_le_mul_left d (show t + 1 ≤ c by omega); rw [Nat.mul_succ] at this; omega
  have hacc : digits d ((List.range t).map fun u => V (c - t + u)) < 2 ^ (d * t) :=
    digits_map_lt fun u hu => hVlt _ (by omega)
  have hlt : 2 ^ (d * t) * 2 ^ d ≤ 2 ^ 40 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hdt
  have hv := hVlt (c - 1 - t) (by omega)
  have hpd : 2 ^ d ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hd
  have hA : digits d ((List.range t).map fun u => V (c - t + u)) * 2 ^ d < 2 ^ 40 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hacc (Nat.two_pow_pos d)) hlt
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

/-- The `b` bytes of `r10` stored at `r8`. -/
theorem ceStores_ok {b : Nat} (hb : b ≤ 8) (s : State)
    (hout : ∀ k < b, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1) :
    WP isa (.block ((List.range b).flatMap ceStore)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) b (fun k => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * k))) ∧
        Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = (s.gpr .r10).toNat / 2 ^ (8 * k) ∧
    Written s.mem s'.mem (s.gpr .r8) k (fun t => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * t))))
    (fun k s' hk ⟨hkp, hr, hw⟩ => ?_) b (Nat.le_refl _) s ⟨Keep.refl _ _, by simp, Written.nil _ _ _⟩)
    fun s' ⟨hkp, _, hw⟩ => ⟨hw, hkp⟩
  have h8 : s'.gpr .r8 = s.gpr .r8 := hkp.gpr (by decide)
  refine WP.mono (ceStore_ok k s' (by rw [hkp.2.2, h8]; exact hout k hk))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8]
    refine (hw.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k
    · subst e; rw [ifp rfl, b8_eq64, hr]
    · rw [ifn e]

/-! ## Decoding -/

theorem ddByte_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (ddByte k)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight 56 + BitVec.setWidth 64 (s.mem (s.gpr .rdi + BitVec.ofNat 64 k)) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddByte
  xrun [hin]

/-- The `b` bytes of a group, from the last, into `r10`. -/
theorem ddBytes_ok {b : Nat} (hb : b ≤ 5) (s : State)
    (hin : ∀ k < b, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) (h0 : s.gpr .r10 = 0) :
    WP isa (.block ((List.range b).flatMap fun t => ddByte (b - 1 - t))) s fun s' =>
      (s'.gpr .r10).toNat = digits 8 ((List.range b).map fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 k)).toNat) ∧
        s'.mem = s.mem ∧ Keep [.rax, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .r10] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - t + u))).toNat))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) b (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, hk⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := hk.gpr (by decide)
  refine WP.mono (ddByte_ok (b - 1 - t) s' (by rw [hk.2.1, hk.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hacc : digits 8 ((List.range t).map fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - t + u))).toNat) <
      2 ^ (8 * t) := digits_map_lt fun u _ => BitVec.isLt _
  have hlt : 2 ^ (8 * t) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have hv := (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - 1 - t))).isLt
  rw [h10, BitVec.toNat_add, rotr_toNat _ (by decide) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))), hr, hdi, hm,
    toNat_setWidth64_8,
    digits_range_succ, show 64 - 56 = 8 by rfl, show b - (t + 1) + 0 = b - 1 - t by omega]
  have e : (fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - (t + 1) + (u + 1)))).toNat) =
      fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - t + u))).toNat := by
    funext u; rw [show b - (t + 1) + (u + 1) = b - t + u by omega]
  have hA : digits 8 ((List.range t).map fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - t + u))).toNat) * 2 ^ 8
      < 2 ^ 40 := by
    have := Nat.mul_lt_mul_of_pos_right hacc (show 0 < 2 ^ 8 by decide)
    have h' : 2 ^ (8 * t) * 2 ^ 8 ≤ 2 ^ 40 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [e]
  have h64 : digits 8 ((List.range t).map fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - t + u))).toNat) *
      2 ^ 8 + (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - 1 - t))).toNat < 2 ^ 64 := by
    have := (s.mem (s.gpr .rdi + BitVec.ofNat 64 (b - 1 - t))).isLt
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hA (Nat.le_of_lt_succ this)) (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.add_comm, Nat.mul_comm]

/-- The word `ddCoef` stores, from the accumulator `a`, with `q` in `r9`. -/
def ddW (d : Nat) (a M : BitVec 64) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&&
    BitVec.ofNat 32 (2 ^ d - 1))).toNat * M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))) >>> d)

theorem ddW_toNat {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 10) (a : BitVec 64) {M : BitVec 64} (hM : M.toNat = 3329) :
    (ddW d a M).toNat = (3329 * (a.toNat % 2 ^ d) + 2 ^ (d - 1)) / 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hd
  have hp' : 2 ^ (d - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hy : (BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat = a.toNat % 2 ^ d := by
    rw [toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hyl : a.toNat % 2 ^ d < 2 ^ 10 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) hp
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

theorem ddCoef_ok (d j : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 10) (s : State)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ddCoef d j)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (ddW d (s.gpr .r10) (s.gpr .r9)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> d) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddCoef
  xrun [hout, show 1 ≤ d by omega, show d ≤ 63 by omega, ddW,
    sx_ofNat (show 2 ^ (d - 1) < 2 ^ 31 from Nat.pow_lt_pow_right (by decide) (by omega))]

/-- The `c` values of a group, decompressed, to `rsi`. -/
theorem ddCoefs_ok {d c : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 10) (hc : c ≤ 8) (s : State)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block ((List.range c).flatMap (ddCoef d))) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
        ddW d (s.gpr .r10 >>> (d * j)) (s.gpr .r9)) ∧
      Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .rdx, .r10] s s' ∧
    s'.gpr .r10 = s.gpr .r10 >>> (d * j) ∧ Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
    ∀ t < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * t)) 32 = ddW d (s.gpr .r10 >>> (d * t)) (s.gpr .r9))
    (fun j s' hj ⟨hk, hr, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, by simp, Frame.refl _ _, fun _ h => absurd h (by omega)⟩)
    fun s' ⟨hk, _, hf, hw⟩ => ⟨hw, hf, hk⟩
  have hsi : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk.gpr (by decide)
  refine WP.mono (ddCoef_ok d j hd1 hd s' (by rw [hk.2.2, hsi]; exact hout j hj))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, ?_, fun t ht => ?_⟩
  · rw [h10, hr, ← BitVec.shiftRight_add, Nat.mul_succ]
  · rw [hm, hsi]
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
