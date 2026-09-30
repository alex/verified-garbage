import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Stream

/-!
# ML-DSA on x86-64: streaming fields through `r10`

Untrusted: everything here is checked by Lean. The group bodies of
`Impl/MlDsa/X86_64/Pack/Stream.lean`, for any width `d`, group of `c`
fields and `nb` bytes, and any code `ld` that loads a field's value
(`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator is a slice of the number throughout (`Pack/Stream.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep Written Written.nil
  Written.snoc Written.congr Written.frame rotr_toNat shr_toNat b8_eq64 ifp ifn sx_ofNat r10zero_ok)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- `r10 ← r10 + rax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State) (hx : (s.gpr .rax).toNat < 2 ^ (64 - sh))
    (hs : (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .r10).toNat = (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  by_cases h : sh = 0
  · subst h
    refine WP.keep _ ?_ (by decide)
    simp only [shiftAdd, ite_true, List.nil_append]
    xrun
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · refine WP.keep _ ?_ (by simp only [shiftAdd, h, ite_false]; rfl)
    simp only [shiftAdd, h, ite_false, List.singleton_append]
    xrun [show 1 ≤ 64 - sh by omega, show 64 - sh ≤ 63 by omega]
    rw [BitVec.toNat_add, rotr_toNat _ (by omega) hx, show 64 - (64 - sh) = sh by omega, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 t) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [ea_at', hout]

/-- The bytes `k, …, k + nf - 1` of the output from the accumulator `X`,
whose byte `u` is byte `k + u` of the output. -/
theorem flush_ok {k nf : Nat} {m₀ : Mem} {o : Addr} {V8 : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V8 (k + u)) (hk : k + nf < 2 ^ 64) (s : State)
    (h8 : s.gpr .r8 = o) (hout : ∀ u < nf, InRegions s.wr (o + BitVec.ofNat 64 (k + u)) 1)
    (hw : Written m₀ s.mem o k V8) (hr : (s.gpr .r10).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      Written m₀ s'.mem o (k + nf) V8 ∧ (s'.gpr .r10).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = X / 2 ^ (8 * u) ∧ Written m₀ s'.mem o (k + u) V8)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h8' : s'.gpr .r8 = o := (hkp.gpr (by decide)).trans h8
  refine WP.mono (packByte_ok (k + u) s' (by rw [hkp.2.2, h8']; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8']
    refine (hw'.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k + u
    · subst e; rw [ifp rfl, b8_eq64, hr', hX u hu]
    · rw [ifn e]

/-- `ld j` loads into `rax` the value `F` of the word at `rdi + 4j`, and
writes only `rax` and `r11`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) : Prop :=
  ∀ j s, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .rax).toNat = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r11] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r10`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (s.gpr .r8) (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) (hj : d * (j + 1) < 2 ^ 32) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (s.gpr .r8) (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.rax, .r10, .r11] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .rax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega) s₁
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))) (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hX : (s₂.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8 : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (o := s.gpr .r8)
    (V8 := bytesOf G) _ (fun u hu => ?_) (by omega) s₂ h8 (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
      omega] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
      omega]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r8`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 (4 * j), 4⟩ ⟨s.gpr .r8, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) nb (bytesOf (digits d ((List.range c).map fun j =>
          F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 nb ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rdi, .r8, .r10, .r11] s s' := by
  generalize hG : digits d ((List.range c).map fun j => F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = s.gpr .rdi := k₁.gpr (by decide)
  have r8₁ : s₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r10, .r11] s₁ s' ∧
      Written s.mem s'.mem (s.gpr .r8) (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have r8 : s'.gpr .r8 = s.gpr .r8 := (hk.gpr (by decide)).trans r8₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    have hj32 := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega)
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd s' (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2, r8]; exact hout t (by omega)) (by rw [r8]; exact hw) hr (by omega))
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), by rw [← r8]; exact hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [di, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨s.gpr .r8, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega
    have := Nat.mul_le_mul hd hc
    rw [hc8] at hw₂
    refine WP.mono (Proof.MlKem.X86_64.CE.tail_ok c nb (by omega) (by omega) s₂)
      fun s₃ ⟨⟨di₃, r8₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [r8₃, k₂.gpr (by decide), r8₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

theorem unpackByte_ok (d j t : Nat) (hsh : 8 * t - d * j ≤ 56) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .r10).toNat + (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .r10).toNat =
          (s.gpr .r10).toNat + (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r10] s s' := by
  unfold unpackByte
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.gpr .rax = BitVec.setWidth 64 (s.mem (s.gpr .rdi +
    BitVec.ofNat 64 t)) ∧ s'.mem = s.mem) (by xrun [ea_at', hin]) (by rfl)) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hb := (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).isLt
  have hax : (s₁.gpr .rax).toNat = (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat := by
    rw [ax₁, Proof.MlKem.X86_64.toNat_setWidth64_8]
  refine WP.mono (shiftAdd_ok (by omega) s₁ (by
      rw [hax]; exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (s.gpr .rdi + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r10).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r10).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.rax, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.rax, .r10] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have di : s'.gpr .rdi = s.gpr .rdi := hkp.gpr (by decide)
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← di] at hbu
  have hbl : (s'.mem (s'.gpr .rdi + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok d j (k + u) (by omega) s' (by rw [hkp.2.1, hkp.2.2, di]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `rax` to
`rsi + 4j`, and writes only `rax` and `r11`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .rax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (s.gpr .rax).toNat) ∧ Keep [.rax, .r11] s s'

theorem extract_ok (d : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block [.mov .rax (.reg .r10), .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))),
      .shift .shr .r10 d]) s fun s' =>
      ((s'.gpr .rax).toNat = (s.gpr .r10).toNat % 2 ^ d ∧ s'.gpr .r10 = s.gpr .r10 >>> d ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [show 1 ≤ d by omega, show d ≤ 63 by omega]
  have hp : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- Field `j`: the bytes it needs into `r10`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (s : State)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4)
    (hr : (s.gpr .r10).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r10).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.rax, .r10, .r11] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) s (fun u hu => hin _ (by omega))
    (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (extract_ok d hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .rax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have si : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, si]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, si, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, shr_toNat, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `rdi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : ∀ t < nb, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 t, 1⟩ ⟨s.gpr .rsi, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 nb ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rsi, .rdi, .r10, .r11] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = s.gpr .rdi := k₁.gpr (by decide)
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r10, .r11] s₁ s' ∧
      Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r10).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have si : s'.gpr .rsi = s.gpr .rsi := (hk.gpr (by decide)).trans si₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) s'
      (fun t ht => by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin t (by omega))
      (fun t ht => by
        rw [di, hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t (by omega) _ (Region.contains_self _ _))
      (by rw [hk.2.2, k₁.2.2, si]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', si]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', si]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (Proof.MlKem.X86_64.DD.tail_ok c nb (by omega) (by omega) s₂)
      fun s₃ ⟨⟨di₃, si₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86_64.Pack
