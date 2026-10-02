import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on AArch64: streaming fields through `x9`

The group bodies of `Impl/MlDsa/AArch64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients, which the
  caller says are bytes `gb, …, gb + nb - 1` of the output (`BytesUpTo`);
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's, which the caller says is
  coefficient `gc + j` of the output (`CoeffsUpTo`).

The accumulator is a slice of the number throughout (`Pack/Stream.lean`).
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_lsl wp_lsr wp_and wp_strb wp_ldrb wp_nil wp_movz wp_addImm
  wp_subImm toNat_add_n toNat_lsl_n toNat_lsr toNat_and_mask toNat_byte toNat_imm setWidth8_of_toNat BytesUpTo
  BytesUpTo.write ptr_add ptr_zero)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

/-- `x9 ← x9 + x10 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State)
    (hs : (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      (s'.gpr .x9).toNat = (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ sh ∧ Only [.x9, .x10] s s' := by
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ↓reduceIte, List.nil_append]
    refine wp_add fun s₁ h₁ e₁ => wp_nil ⟨?_, h₁.mono⟩
    rw [Nat.pow_zero, Nat.mul_one] at hs ⊢
    rw [e₁, toNat_add_n hs]
  · simp only [shiftAdd, h, ↓reduceIte, List.singleton_append]
    have hx : (s.gpr .x10).toNat * 2 ^ sh < 2 ^ 64 := by omega
    refine wp_lsl hsh fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => wp_nil ⟨?_, (h₁.trans h₂).mono⟩
    have v₁ : (s₁.gpr .x10).toNat = (s.gpr .x10).toNat * 2 ^ sh := by rw [e₁, toNat_lsl_n hx]
    rw [e₂, h₁.get .x9, toNat_add_n (by rw [v₁]; omega), v₁]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 4096) (s : State)
    (hout : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 t) ((s.gpr .x9).setWidth 8) ∧
        s'.gpr .x9 = s.gpr .x9 >>> 8 ∧ Keep [.x9] s s' :=
  wp_strb ht rfl hout fun s₁ h₁ => wp_lsr (by decide) fun s₂ h₂ e₂ =>
    wp_nil ⟨by rw [h₂.mem, h₁.mem], by rw [e₂, h₁.gpr], (h₁.keep.trans h₂.keep).mono⟩

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- The bytes `k, …, k + nf - 1` of the group at `x2 = o + gb` from the
accumulator `X`, whose byte `u` is byte `gb + k + u` of the output. -/
theorem flush_ok {gb k nf N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = L (gb + k + u)) (hN : gb + k + nf ≤ N)
    (hN64 : N < 2 ^ 64) (hk : k + nf ≤ 4096) (s : State) (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb)
    (hR : (⟨o, N⟩ : Region) ∈ s.wr) (hw : BytesUpTo s.mem o N (gb + k) L old)
    (hf : Frame [⟨o, N⟩] m₀ s.mem) (hr : (s.gpr .x9).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      BytesUpTo s'.mem o N (gb + k + nf) L old ∧ Frame [⟨o, N⟩] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = X / 2 ^ (8 * nf) ∧ Keep [.x9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.x9] s s' ∧
    (s'.gpr .x9).toNat = X / 2 ^ (8 * u) ∧ BytesUpTo s'.mem o N (gb + k + u) L old ∧
      Frame [⟨o, N⟩] m₀ s'.mem)
    (fun u s' hu ⟨hkp, hr', hw', hf'⟩ => ?_) nf (Nat.le_refl _) s
    ⟨Keep.refl _ _, by rw [hr, Nat.mul_zero, Nat.pow_zero, Nat.div_one], hw, hf⟩)
    fun s' ⟨hkp, hr', hw', hf'⟩ => ⟨hw', hf', hr', hkp⟩
  have ha : s'.gpr .x2 + BitVec.ofNat 64 (k + u) = o + BitVec.ofNat 64 (gb + k + u) := by
    rw [hkp.get .x2, h2, ptr_add, Nat.add_assoc]
  have hc : (⟨o, N⟩ : Region).Contains (o + BitVec.ofNat 64 (gb + k + u)) 1 :=
    Offset.contains_base o (by omega) (by omega)
  refine WP.mono (packByte_ok (by omega) s' (by rw [ha, hkp.wr]; exact ⟨_, hR, hc⟩))
    fun s'' ⟨hm, h9, hk'⟩ => ⟨(hkp.trans hk').mono, ?_, ?_, ?_⟩
  · rw [h9, toNat_lsr, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ha, show gb + k + (u + 1) = gb + k + u + 1 by omega]
    exact hw'.write (by omega) (by omega) (by rw [setWidth8_of_toNat hr', hX u hu])
  · rw [hm, ha]
    exact hf'.writeW (List.mem_singleton_self _) _ hc

/-- `ld j` loads into `x10` the value `F` of the word at `x0 + 4j`, and
writes only `x10` and `x14`, when `x12` and `x13` hold `K12` and `K13`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) (K12 K13 : BitVec 64) : Prop :=
  ∀ j s, s.gpr .x12 = K12 → s.gpr .x13 = K13 → 4 * j < 16384 →
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      (s'.gpr .x10).toNat = F (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) ∧ Only [.x10, .x14] s s'

/-- Field `j`: its value, digit `j` of `G`, into `x9`, then the bytes it
completes, bytes `gb + ⌊dj/8⌋, …` of the output. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64}
    (hld : LdOk ld F K12 K13) {d j G gb N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem}
    (hd : d ≤ 20) (hj : j < 8) (hN : gb + d * (j + 1) / 8 ≤ N) (hN64 : N < 2 ^ 64)
    (hL : ∀ t < d * (j + 1) / 8, L (gb + t) = bytesOf G t) (s : State) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb) (hR : (⟨o, N⟩ : Region) ∈ s.wr)
    (hw : BytesUpTo s.mem o N (gb + d * j / 8) L old) (hf : Frame [⟨o, N⟩] m₀ s.mem)
    (hr : (s.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      BytesUpTo s'.mem o N (gb + d * (j + 1) / 8) L old ∧ Frame [⟨o, N⟩] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.x9, .x10, .x14] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s h12 h13 (by omega) hin) fun s₁ ⟨ax₁, o₁⟩ => ?_
  have hx : (s₁.gpr .x10).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [o₁.get .x9, hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega)) fun s₂ ⟨r₂, o₂⟩ => ?_
  have hX : (s₂.gpr .x9).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
  have hn' : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega
  have h8 : d * (j + 1) ≤ 160 := by have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  refine WP.mono (flush_ok (gb := gb) (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (N := N) (L := L)
      (old := old) (m₀ := m₀) _ (fun u hu => ?_) (by omega) hN64 (by omega) s₂
      (by rw [o₂.get .x2, o₁.get .x2, h2]) (by rw [o₂.wr, o₁.wr]; exact hR)
      (by rw [o₂.mem, o₁.mem]; exact hw) (by rw [o₂.mem, o₁.mem]; exact hf) hX)
    fun s₃ ⟨hw₃, hf₃, hr₃, k₃⟩ => ⟨?_, hf₃, ?_, ((o₁.keep.trans o₂.keep).trans k₃).mono⟩
  · rw [Nat.add_assoc, hL _ (by omega)]
    refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by omega)]
  · rwa [Nat.add_assoc, hn'] at hw₃
  · rw [hr₃, pack_shift, hn']

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values `V` of its `c` coefficients, stored at `x2 = o + gb`: bytes
`gb, …, gb + nb - 1` of the output, whose other bytes `m₀` had. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64}
    (hld : LdOk ld F K12 K13) {d c nb gb N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hN : gb + nb ≤ N) (hN64 : N < 2 ^ 64)
    {V : Nat → Nat} (hV : ∀ j < c, V j < 2 ^ d)
    (hL : ∀ t < nb, L (gb + t) = bytesOf (digits d ((List.range c).map V)) t) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : ∀ j < c, ∀ m, Frame [⟨o, N⟩] m₀ m → F (m.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) = V j)
    (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb) (hR : (⟨o, N⟩ : Region) ∈ s.wr)
    (hw : BytesUpTo s.mem o N gb L old) (hf : Frame [⟨o, N⟩] m₀ s.mem) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      BytesUpTo s'.mem o N (gb + nb) L old ∧ Frame [⟨o, N⟩] m₀ s'.mem ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 nb ∧
        s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧ Keep [.x0, .x2, .x9, .x10, .x11, .x14] s s' := by
  generalize hG : digits d ((List.range c).map V) = G at hL
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = V j := fun j hj => by rw [← hG]; exact digits_range_get hV hj
  have hdc8 : d * c / 8 = nb := by omega
  have := Nat.mul_le_mul hd hc
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movz fun s₁ o₁ e₁ => wp_nil ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.x9, .x10, .x14] s₁ s' ∧
      BytesUpTo s'.mem o N (gb + d * j / 8) L old ∧ Frame [⟨o, N⟩] m₀ s'.mem ∧
      (s'.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw', hf', hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [o₁.mem, Nat.mul_zero, Nat.zero_div, Nat.add_zero]; exact hw, by rw [o₁.mem]; exact hf,
      by rw [e₁, toNat_imm, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, hf₂, _⟩ => ?_
  · have hx0 : s'.gpr .x0 = s.gpr .x0 := by rw [hk.get .x0, o₁.get .x0]
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      rw [← hdc8]; exact Nat.div_le_div_right (Nat.mul_le_mul_left d hj)
    refine WP.mono (packCoef_ok hld (G := G) (N := N) (L := L) (old := old) (m₀ := m₀) hd (by omega)
      (by omega) hN64 (fun t ht => hL t (by omega)) s' (by rw [hk.get .x12, o₁.get .x12, h12])
      (by rw [hk.get .x13, o₁.get .x13, h13]) (by rw [hk.rd, hk.wr, o₁.rd, o₁.wr, hx0]; exact hin j hj)
      (by rw [hx0, hv j hj _ hf', hdig j hj]) (by rw [hk.get .x2, o₁.get .x2, h2])
      (by rw [hk.wr, o₁.wr]; exact hR) hw' hf' hr)
      fun s'' ⟨hw'', hf'', hr', hk'⟩ => ⟨(hk.trans hk').mono, hw'', hf'', hr'⟩
  · rw [hdc8] at hw₂
    refine wp_addImm (by omega) fun s₃ o₃ e₃ => wp_addImm (by omega) fun s₄ o₄ e₄ =>
      wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hw₂
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hf₂
    · rw [o₅.get .x0, o₄.get .x0, e₃, k₂.get .x0, o₁.get .x0]
    · rw [o₅.get .x2, e₄, o₃.get .x2, k₂.get .x2, o₁.get .x2]
    · rw [e₅, o₄.get .x11, o₃.get .x11, k₂.get .x11, o₁.get .x11]
    · exact ((((o₁.keep.trans k₂).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono

/-! ## Unpacking -/

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j ≤ 56) (ht : t < 4096) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .x9).toNat + (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      (s'.gpr .x9).toNat =
          (s.gpr .x9).toNat + (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        Only [.x9, .x10] s s' := by
  unfold unpackByte
  rw [List.singleton_append]
  refine wp_ldrb ht rfl hin fun s₁ o₁ e₁ => ?_
  have hax : (s₁.gpr .x10).toNat = (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat := by rw [e₁, toNat_byte]
  refine WP.mono (shiftAdd_ok (by omega) s₁ (by rw [hax, o₁.get .x9]; exact hs))
    fun s₂ ⟨r₂, o₂⟩ => ⟨by rw [r₂, hax, o₁.get .x9], (o₁.trans o₂).mono⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk4 : k + nl ≤ 4096) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (s.gpr .x0 + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .x9).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .x9).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ Only [.x9, .x10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Only [.x9, .x10] s s' ∧
    (s'.gpr .x9).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Only.refl _ _, hr⟩)
    fun s' ⟨hkp, hr'⟩ => ⟨hr', hkp⟩
  have di : s'.gpr .x0 = s.gpr .x0 := hkp.get .x0
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hkp.mem, ← di] at hbu
  have hbl : (s'.mem (s'.gpr .x0 + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok (by omega) (by omega) s' (by rw [hkp.rd, hkp.wr, di]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨r'', k''⟩ => ⟨(hkp.trans k'').mono, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `x10` to
`x4 + 4j`, and writes only `x10` and `x14`, when `x12` and `x13` hold `K12`
and `K13`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) (K12 K13 : BitVec 64) : Prop :=
  ∀ j s, s.gpr .x12 = K12 → s.gpr .x13 = K13 → 4 * j < 16384 →
    InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .x10).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x4 + BitVec.ofNat 64 (4 * j)) (W (s.gpr .x10).toNat) ∧ Keep [.x10, .x14] s s'

theorem extract_ok {d : Nat} (hd : d < 64) (s : State) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1) :
    WP isa (.block [.logic .and .x .x10 .x9 .x15, .lsr .x .x9 .x9 d]) s fun s' =>
      (s'.gpr .x10).toNat = (s.gpr .x9).toNat % 2 ^ d ∧ s'.gpr .x9 = s.gpr .x9 >>> d ∧ Only [.x9, .x10] s s' :=
  wp_and fun s₁ o₁ e₁ => wp_lsr hd fun s₂ o₂ e₂ =>
    wp_nil ⟨by rw [o₂.get .x10, e₁, toNat_and_mask _ _ h15], by rw [e₂, o₁.get .x9], (o₁.trans o₂).mono⟩

/-- Field `j`: the bytes it needs into `x9`, then its value, digit `j` of
`H`, stored by `fin` as coefficient `gc + j` of the output at `p`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {K12 K13 : BitVec 64}
    (hfin : FinOk fin d W K12 K13) (hd : d ≤ 20) {H j gc : Nat} {p : Addr} {Wf old : Nat → BitVec 32}
    {m₀ : Mem} (hj : j < 8) (hgc : gc + j < 256) (hW : Wf (gc + j) = W (H / 2 ^ (d * j) % 2 ^ d)) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (h4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * gc)) (hP : polyRegion p ∈ s.wr)
    (hw : CoeffsUpTo s.mem p (gc + j) Wf old) (hf : Frame [polyRegion p] m₀ s.mem)
    (hr : (s.gpr .x9).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      CoeffsUpTo s'.mem p (gc + j + 1) Wf old ∧ Frame [polyRegion p] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧
        Keep [.x9, .x10, .x14] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  have h8 : d * (j + 1) ≤ 160 := by have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) (by rw [hn']; unfold need; omega) s
    (fun u hu => hin _ (by omega)) (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, o₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (extract_ok (by omega) s₁ (by rw [o₁.get .x15, h15])) fun s₂ ⟨ax₂, r₂, o₂⟩ => ?_
  have hv : (s₂.gpr .x10).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have hx4 : s₂.gpr .x4 = s.gpr .x4 := by rw [o₂.get .x4, o₁.get .x4]
  have ha : s₂.gpr .x4 + BitVec.ofNat 64 (4 * j) = coeffAddr p (gc + j) := by
    rw [hx4, h4, ptr_add, ← Nat.mul_add]
  have hc : (polyRegion p).Contains (coeffAddr p (gc + j)) 4 := coeff_contains p hgc
  refine WP.mono (hfin j s₂ (by rw [o₂.get .x12, o₁.get .x12, h12]) (by rw [o₂.get .x13, o₁.get .x13, h13])
      (by omega) (by rw [ha, o₂.wr, o₁.wr]; exact ⟨_, hP, hc⟩) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨?_, ?_, ?_, ((o₁.keep.trans o₂.keep).trans k₃).mono⟩
  · rw [m₃, ha, o₂.mem, o₁.mem]
    exact hw.write hgc (by rw [hv, hW])
  · rw [m₃, ha, o₂.mem, o₁.mem]
    exact hf.writeW (List.mem_singleton_self _) _ hc
  · rw [k₃.get .x9, r₂, toNat_lsr, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes `B` at `x0`: coefficient
`gc + j` of the output at `x4 = p + 4 gc`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {K12 K13 : BitVec 64}
    (hfin : FinOk fin d W K12 K13) {c nb gc : Nat} {p : Addr} {Wf old : Nat → BitVec 32} {m₀ : Mem}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hgc : gc + c ≤ 256) {B : Nat → Nat}
    (hW : ∀ j < c, Wf (gc + j) = W (digits 8 ((List.range nb).map B) / 2 ^ (d * j) % 2 ^ d)) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < nb, ∀ m, Frame [polyRegion p] m₀ m → (m (s.gpr .x0 + BitVec.ofNat 64 t)).toNat = B t)
    (h4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * gc)) (hP : polyRegion p ∈ s.wr)
    (hw : CoeffsUpTo s.mem p gc Wf old) (hf : Frame [polyRegion p] m₀ s.mem) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      CoeffsUpTo s'.mem p (gc + c) Wf old ∧ Frame [polyRegion p] m₀ s'.mem ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 nb ∧ s'.gpr .x4 = s.gpr .x4 + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧ Keep [.x0, .x4, .x9, .x10, .x11, .x14] s s' := by
  generalize hH : digits 8 ((List.range nb).map B) = H at hW
  have hB : ∀ t < nb, B t < 2 ^ 8 := fun t ht => by
    rw [← hb t ht s.mem hf]; exact BitVec.isLt _
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = B t :=
    fun t ht => by rw [← hH]; exact digits_range_get hB ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movz fun s₁ o₁ e₁ => wp_nil ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.x9, .x10, .x14] s₁ s' ∧
      CoeffsUpTo s'.mem p (gc + j) Wf old ∧ Frame [polyRegion p] m₀ s'.mem ∧
      (s'.gpr .x9).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hw', hf', hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [o₁.mem, Nat.add_zero]; exact hw, by rw [o₁.mem]; exact hf,
      by rw [e₁, toNat_imm]; simp [need, Nat.mod_one]⟩) fun s₂ ⟨k₂, hw₂, hf₂, _⟩ => ?_
  · have hx0 : s'.gpr .x0 = s.gpr .x0 := by rw [hk.get .x0, o₁.get .x0]
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (unpackCoef_ok hfin hd (H := H) (m₀ := m₀) (by omega) (by omega) (hW j hj) s'
      (by rw [hk.get .x12, o₁.get .x12, h12]) (by rw [hk.get .x13, o₁.get .x13, h13])
      (by rw [hk.get .x15, o₁.get .x15, h15])
      (fun t ht => by rw [hk.rd, hk.wr, o₁.rd, o₁.wr, hx0]; exact hin t (by omega))
      (fun t ht => by rw [hx0, hb t (by omega) _ hf', hbyte t (by omega)])
      (by rw [hk.get .x4, o₁.get .x4, h4]) (by rw [hk.wr, o₁.wr]; exact hP) hw' hf' hr)
      fun s'' ⟨hw'', hf'', hr', hk'⟩ => ⟨(hk.trans hk').mono, hw'', hf'', hr'⟩
  · refine wp_addImm (by omega) fun s₃ o₃ e₃ => wp_addImm (by omega) fun s₄ o₄ e₄ =>
      wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hw₂
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hf₂
    · rw [o₅.get .x0, o₄.get .x0, e₃, k₂.get .x0, o₁.get .x0]
    · rw [o₅.get .x4, e₄, o₃.get .x4, k₂.get .x4, o₁.get .x4]
    · rw [e₅, o₄.get .x11, o₃.get .x11, k₂.get .x11, o₁.get .x11]
    · exact ((((o₁.keep.trans k₂).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono

end VG.Proof.MlDsa.AArch64.Pack
