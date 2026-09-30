import VerifiedGarbage.Impl.MlDsa.X86.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Written
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on x86 (32-bit): streaming fields through `ebx`

Untrusted: everything here is checked by Lean. The group bodies of
`Impl/MlDsa/X86/Pack/Stream.lean`, for any width `d`, group of `c` fields
and `nb` bytes, and any code `ld` that loads a field's value (`LdOk`) or
`fin` that stores a coefficient from it (`FinOk`), as on x86-64:

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator is a slice of the number throughout (`Pack/Stream.lean`),
of at most `d + 7 ≤ 27` bits.
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlKem.X86 (rotr_small toNat_shr)
open VG.Proof.MlDsa.Pack

/-- `x + d` of a 32-bit `x`, where nothing wraps around. -/
theorem toNat_add_fit {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).toNat = x.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt h]

/-- `ebx ← ebx + eax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 32) (s : State) (hx : (s.gpr .eax).toNat < 2 ^ (32 - sh))
    (hs : (s.gpr .ebx).toNat + (s.gpr .eax).toNat * 2 ^ sh < 2 ^ 32) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .ebx).toNat = (s.gpr .ebx).toNat + (s.gpr .eax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.eax, .ebx] s s' := by
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
    xrun [show 1 ≤ 32 - sh by omega, show 32 - sh ≤ 31 by omega, and_self]
    rw [BitVec.toNat_add, rotr_small _ (by omega) (by omega) hx, show 32 - (32 - sh) = sh by omega,
      Nat.mod_eq_of_lt hs]

theorem ebxZero_ok (s : State) :
    WP isa (.block [.mov .ebx (.imm 0)]) s fun s' => (s'.gpr .ebx = 0 ∧ s'.mem = s.mem) ∧
      Keep [.ebx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- The end of a group: the pointers advanced, and the counter down. -/
theorem tail_ok (a b : Nat) (s : State) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 a)), .alu .add .edi (.imm (BitVec.ofNat 32 b)),
      .alu .sub .ecx (.imm 1)]) s fun s' =>
      (s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 a ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 b ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.esi, .edi, .ecx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (addr (s.gpr .edi) t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (addr (s.gpr .edi) t) (BitVec.setWidth 8 (s.gpr .ebx)) ∧
        s'.gpr .ebx = s.gpr .ebx >>> 8) ∧ Keep [.ebx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [hout]

/-- The bytes `k, …, k + nf - 1` of the output from the accumulator `X`,
whose byte `u` is byte `k + u` of the output. -/
theorem flush_ok {k nf : Nat} {m₀ : Mem} {E : BitVec 32} {V8 : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V8 (k + u)) (hk : E.toNat + (k + nf) ≤ 2 ^ 32)
    (s : State) (h8 : s.gpr .edi = E)
    (hout : ∀ u < nf, InRegions s.wr (E.setWidth 64 + BitVec.ofNat 64 (k + u)) 1)
    (hw : Written m₀ s.mem (E.setWidth 64) k V8) (hr : (s.gpr .ebx).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      Written m₀ s'.mem (E.setWidth 64) (k + nf) V8 ∧ (s'.gpr .ebx).toNat = X / 2 ^ (8 * nf) ∧
        Keep [.ebx] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.ebx] s s' ∧
    (s'.gpr .ebx).toNat = X / 2 ^ (8 * u) ∧ Written m₀ s'.mem (E.setWidth 64) (k + u) V8)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h8' : s'.gpr .edi = E := (hkp.gpr (by decide)).trans h8
  have ha : addr (s'.gpr .edi) (k + u) = E.setWidth 64 + BitVec.ofNat 64 (k + u) := by
    rw [h8']; exact addr_of_fit (by omega)
  refine WP.mono (packByte_ok (k + u) s' (by rw [ha, hkp.2.2]; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, toNat_shr, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ha]
    refine (hw'.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k + u
    · subst e; rw [ifp rfl, b8_eq, hr', hX u hu]
    · rw [ifn e]

/-- `ld j` loads into `eax` the value `F` of the word at `esi + 4j`, and
writes only `eax` and `edx`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) : Prop :=
  ∀ j s, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .eax).toNat = F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.eax, .edx] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

theorem div8_le_succ (d j : Nat) : d * j / 8 ≤ d * (j + 1) / 8 :=
  Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)

/-- Field `j`: its value, digit `j` of `G`, into `ebx`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} {E : BitVec 32} (s : State) (h8 : s.gpr .edi = E)
    (hfit : E.toNat + d * (j + 1) / 8 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4)
    (hv : F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (E.setWidth 64 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (E.setWidth 64) (d * j / 8) (bytesOf G))
    (hr : (s.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (E.setWidth 64) (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .ebx).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.eax, .ebx, .edx] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .eax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by
    rw [k₁.gpr (by decide), hr]
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
  have hX : (s₂.gpr .ebx).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8₂ : s₂.gpr .edi = E := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]
  have hle := div8_le_succ d j
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (E := E)
    (V8 := bytesOf G) _ (fun u hu => ?_) (by omega) s₂ h8₂ (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by omega] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by omega]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `edi`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (s : State)
    (hfit : (s.gpr .edi).toNat + nb ≤ 2 ^ 32)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨addr (s.gpr .esi) (4 * j), 4⟩ ⟨(s.gpr .edi).setWidth 64, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem ((s.gpr .edi).setWidth 64) nb (bytesOf (digits d ((List.range c).map fun j =>
          F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32)))) ∧
        s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 nb ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧
        Keep [.eax, .ecx, .edx, .ebx, .esi, .edi] s s' := by
  generalize hG : digits d ((List.range c).map fun j => F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ebxZero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have si₁ : s₁.gpr .esi = s.gpr .esi := k₁.gpr (by decide)
  have di₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.eax, .ebx, .edx] s₁ s' ∧
      Written s.mem s'.mem ((s.gpr .edi).setWidth 64) (d * j / 8) (bytesOf G) ∧
      (s'.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have si : s'.gpr .esi = s.gpr .esi := (hk.gpr (by decide)).trans si₁
    have di : s'.gpr .edi = s.gpr .edi := (hk.gpr (by decide)).trans di₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd s' di (by omega)
      (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, si]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2]; exact hout t (by omega)) hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [si, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨(s.gpr .edi).setWidth 64, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega
    rw [hc8] at hw₂
    refine WP.mono (tail_ok (4 * c) nb s₂)
      fun s₃ ⟨⟨si₃, di₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

theorem unpackByte_ok (d j t : Nat) (hsh : 8 * t - d * j ≤ 24) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hs : (s.gpr .ebx).toNat + (s.mem (addr (s.gpr .esi) t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 32) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .ebx).toNat =
          (s.gpr .ebx).toNat + (s.mem (addr (s.gpr .esi) t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.eax, .ebx] s s' := by
  unfold unpackByte
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax] (Q := fun s' => s'.gpr .eax = BitVec.setWidth 32 (s.mem (addr (s.gpr .esi) t)) ∧
    s'.mem = s.mem) (by xrun [hin]) (by rfl)) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hb := (s.mem (addr (s.gpr .esi) t)).isLt
  have hax : (s₁.gpr .eax).toNat = (s.mem (addr (s.gpr .esi) t)).toNat := by
    rw [ax₁, toNat_setWidth32_8]
  refine WP.mono (shiftAdd_ok (by omega) s₁ (by
      rw [hax]; exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (addr (s.gpr .esi) (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .ebx).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .ebx).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.eax, .ebx] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.eax, .ebx] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .ebx).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have si : s'.gpr .esi = s.gpr .esi := hkp.gpr (by decide)
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← si] at hbu
  have hbl : (s'.mem (addr (s'.gpr .esi) (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok d j (k + u) (by omega) s' (by rw [hkp.2.1, hkp.2.2, si]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `eax` to
`edi + 4j`, and writes only `eax` and `edx`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (addr (s.gpr .edi) (4 * j)) 4 → (s.gpr .eax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .edi) (4 * j)) (W (s.gpr .eax).toNat) ∧ Keep [.eax, .edx] s s'

theorem extract_ok (d : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1))),
      .shift .shr .ebx d]) s fun s' =>
      ((s'.gpr .eax).toNat = (s.gpr .ebx).toNat % 2 ^ d ∧ s'.gpr .ebx = s.gpr .ebx >>> d ∧ s'.mem = s.mem) ∧
        Keep [.eax, .ebx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [show 1 ≤ d by omega, show d ≤ 31 by omega, and_self]
  exact Proof.MlKem.X86.toNat_and_mask _ _ (by omega)

/-- Field `j`: the bytes it needs into `ebx`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (s : State)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (addr (s.gpr .esi) t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (addr (s.gpr .edi) (4 * j)) 4)
    (hr : (s.gpr .ebx).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .edi) (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .ebx).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧
        Keep [.eax, .ebx, .edx] s s' := by
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
  have hv : (s₂.gpr .eax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have di : s₂.gpr .edi = s.gpr .edi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, di]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, di, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, toNat_shr, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `esi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hfit : (s.gpr .edi).toNat + 4 * c ≤ 2 ^ 32)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hout : ∀ j < c, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : ∀ t < nb, Region.Disjoint ⟨addr (s.gpr .esi) t, 1⟩ ⟨(s.gpr .edi).setWidth 64, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (addr (s.gpr .esi) t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨(s.gpr .edi).setWidth 64, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 nb ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧
        Keep [.eax, .ecx, .edx, .ebx, .esi, .edi] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (addr (s.gpr .esi) t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (addr (s.gpr .esi) t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  generalize hP : (s.gpr .edi).setWidth 64 = P at hout hsep ⊢
  have ha : ∀ j < c, addr (s.gpr .edi) (4 * j) = P + BitVec.ofNat 64 (4 * j) := fun j hj => by
    rw [← hP]; exact addr_of_fit (by omega)
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ebxZero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have si₁ : s₁.gpr .esi = s.gpr .esi := k₁.gpr (by decide)
  have di₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.eax, .ebx, .edx] s₁ s' ∧
      Frame [⟨P, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (P + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .ebx).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have si : s'.gpr .esi = s.gpr .esi := (hk.gpr (by decide)).trans si₁
    have di : s'.gpr .edi = s.gpr .edi := (hk.gpr (by decide)).trans di₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) s'
      (fun t ht => by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, si]; exact hin t (by omega))
      (fun t ht => by
        rw [si, hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t (by omega) _ (Region.contains_self _ _))
      (by rw [hk.2.2, k₁.2.2, di, ha j hj]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', di, ha j hj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', di, ha j hj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (tail_ok nb (4 * c) s₂)
      fun s₃ ⟨⟨si₃, di₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj]
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86.Pack
