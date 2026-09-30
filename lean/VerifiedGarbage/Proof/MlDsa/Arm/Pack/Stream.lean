import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Stream

/-!
# ML-DSA on 32-bit ARM: streaming fields through `r3`

Untrusted: everything here is checked by Lean. The group bodies of
`Impl/MlDsa/Arm/Pack/Stream.lean`, for any width `d`, group of `c` fields
and `nb` bytes, and any code `ld` that loads a field's value (`LdOk`) or
`fin` that stores a coefficient from it (`FinOk`), as on x86-64:

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator `r3` is a slice of the number throughout
(`Proof/MlDsa/Pack/Stream.lean`), of at most `d + 7 ≤ 27` bits.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Proof.MlKem.Arm (byte_writeW8 contains_off setWidth8 setWidth32_toNat)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

/-! ## Registers kept -/

/-- `s'` has the registers of `s` but for `rs`, and its regions and stack pointer. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => match dstOf i with
    | some r => rs.contains r
    | none => true

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  refine ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi e => hr ?_) he', r, w, p⟩
  have := List.all_eq_true.mp hc i hi
  simp only [e, List.contains_iff_mem] at this
  exact this

/-! ## Instructions -/

/-- `r3 ← r3 + r12 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh ≤ 31) (s : State)
    (hs : (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32) :
    WP isa (.block [shiftAdd sh]) s fun s' =>
      ((s'.gpr .r3).toNat = (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ite_true]
    run_block [and_true]
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · simp only [shiftAdd, h, ite_false]
    run_block [show 1 ≤ sh by omega, hsh, and_true]
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 4096) (s : State)
    (hout : InRegions s.wr (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) (BitVec.ofNat 8 (s.gpr .r3).toNat) ∧
        (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ 8) ∧ Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  unfold packByte
  run_block [ht, hout, and_true]
  exact ⟨by rw [setWidth8], by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩

/-- The first `n` bytes of the group of `nb` bytes at `o` are `V 0, …, V (n - 1)`,
and memory is `m₀`'s outside the group. -/
def GOut (m₀ m : Mem) (o : Addr) (nb n : Nat) (V : Nat → Byte) : Prop :=
  Frame [⟨o, nb⟩] m₀ m ∧ ∀ t < n, m (o + BitVec.ofNat 64 t) = V t

/-- The bytes `k, …, k + nf - 1` of the group from the accumulator `X`,
whose byte `u` is byte `k + u` of the group. -/
theorem flush_ok {k nf nb : Nat} {m₀ : Mem} {o : Addr} {y : BitVec 32} {V : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V (k + u)) (hk : k + nf ≤ nb) (hnb : nb < 4096)
    (s : State) (h2 : s.gpr .r2 = y) (ho : ∀ t < nb, State.addr (y + BitVec.ofNat 32 t) = o + BitVec.ofNat 64 t)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hw : GOut m₀ s.mem o nb k V) (hr : (s.gpr .r3).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      GOut m₀ s'.mem o nb (k + nf) V ∧ (s'.gpr .r3).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r3] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r3] s s' ∧
    (s'.gpr .r3).toNat = X / 2 ^ (8 * u) ∧ GOut m₀ s'.mem o nb (k + u) V)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h2' : s'.gpr .r2 = y := (hkp.gpr (by decide)).trans h2
  have ea : State.addr (s'.gpr .r2 + BitVec.ofNat 32 (k + u)) = o + BitVec.ofNat 64 (k + u) := by
    rw [h2']; exact ho _ (by omega)
  refine WP.mono (packByte_ok (by omega) s' (by rw [ea, hkp.2.2.1]; exact hout _ (by omega)))
    fun s'' ⟨⟨hm, h3⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_, ?_⟩
  · rw [h3, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ea]
    exact hw'.1.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · intro t ht
    rw [hm, ea, byte_writeW8 _ _ (by omega) (by omega)]
    by_cases e : t = k + u
    · rw [ite_eq_left e, hr', hX u hu, e]
    · rw [ite_eq_right e]; exact hw'.2 t (by omega)

/-- `ld j` loads into `r12` the value `V` of the word at `r0 + 4j`, and
writes only `r4` and `r12`. -/
def LdOk (ld : Nat → List Instr) (V : BitVec 32 → Nat) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .r12).toNat = V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) ∧
        s'.mem = s.mem) ∧ Keep [.r4, .r12] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r3`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d j nb G : Nat}
    (hd : d ≤ 20) (hj : j < 8) (hnb : nb < 4096) (hjn : d * (j + 1) / 8 ≤ nb) {m₀ : Mem} {o : Addr}
    {y : BitVec 32} (s : State) (h2 : s.gpr .r2 = y)
    (ho : ∀ t < nb, State.addr (y + BitVec.ofNat 32 t) = o + BitVec.ofNat 64 t)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4)
    (hv : V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hw : GOut m₀ s.mem o nb (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      GOut m₀ s'.mem o nb (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.r3, .r4, .r12] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s (by omega) hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .r12).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hX : (s₂.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h2₂ : s₂.gpr .r2 = y := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h2]
  have hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
  have hsum : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (V := bytesOf G) _
    (fun u hu => ?_) (by omega) hnb s₂ h2₂ ho (by rw [k₂.2.2.1, k₁.2.2.1]; exact hout)
    (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨by rwa [hsum] at hw₃, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [hr₃, pack_shift, hsum]

theorem zero_ok (s : State) :
    WP isa (.block [.mov .r3 (.imm 0)]) s fun s' => ((s'.gpr .r3).toNat = 0 ∧ s'.mem = s.mem) ∧ Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

theorem packTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * c))), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 nb)),
      .subs .r1 .r1 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧ s'.mem = s.mem) ∧
        Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r2`. -/
theorem packBody_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State)
    (hx : (s.gpr .r0).toNat + 4 * c ≤ 2 ^ 32) (hy : (s.gpr .r2).toNat + nb ≤ 2 ^ 32)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 t) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), 4 * c⟩ ⟨State.addr (s.gpr .r2), nb⟩)
    (hF : ∀ j < c, V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb nb (bytesOf (digits d ((List.range c).map fun j =>
          V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hG : digits d ((List.range c).map fun j =>
    V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d =
      V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  have ea : ∀ j < c, State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega)
  have ho : ∀ t < nb, State.addr (s.gpr .r2 + BitVec.ofNat 32 t) = State.addr (s.gpr .r2) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega)
  have hnb : nb ≤ 20 := by have := Nat.mul_le_mul hd hc; omega
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  have y₁ : s₁.gpr .r2 = s.gpr .r2 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r3, .r4, .r12] s₁ s' ∧
      GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, ⟨by rw [m₁]; exact Frame.refl _ _, fun t ht => absurd ht (by simp)⟩,
      by rw [z₁, Nat.mul_zero, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]⟩)
    fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    have yj : s'.gpr .r2 = s.gpr .r2 := (hk.gpr (by decide)).trans y₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    have hA : State.addr (s'.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
        State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := by rw [xj]; exact ea j hj
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd (by omega) (by omega) hj8 s' yj ho
      (by rw [hk.2.2.1, k₁.2.2.1]; exact hout) (by rw [hA, hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin j hj)
      ?_ hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [hA, hdig j hj]
    refine congrArg V (hw.1.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_left (Offset.sub_base _ (by omega))
  · have hc8 : d * c / 8 = nb := by omega
    rw [hc8] at hw₂
    refine WP.mono (packTail_ok e₁ e₂ s₂) fun s₃ ⟨⟨x₃, y₃, c₃, z₃, m₃⟩, k₃⟩ =>
      ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [y₃, k₂.gpr (by decide), y₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]

/-! ## Unpacking -/

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j ≤ 31) (ht : t < 4096) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 t)) 1)
    (hs : (s.gpr .r3).toNat + (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat * 2 ^ (8 * t - d * j) <
      2 ^ 32) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .r3).toNat =
          (s.gpr .r3).toNat + (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.r3, .r12] s s' := by
  rw [show unpackByte d j t = ([.ldrb .r12 .r0 t] : List Instr) ++ [shiftAdd (8 * t - d * j)] from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun s' => s'.gpr .r12 =
    (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).setWidth 32 ∧ s'.mem = s.mem)
    (by run_block [ht, hin, and_true]) rfl) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hax : (s₁.gpr .r12).toNat = (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat := by
    rw [ax₁, setWidth32_toNat]
  refine WP.mono (shiftAdd_ok hsh s₁ (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` (at `x`) into the accumulator, which
holds bits `d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} {x : BitVec 32} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk' : k + nl ≤ 4096) (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (k + u))) 1)
    (hb : ∀ u < nl, (s.mem (State.addr (x + BitVec.ofNat 32 (k + u)))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.r3, .r12] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r3, .r12] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have x' : s'.gpr .r0 = x := (hkp.gpr (by decide)).trans h0
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← x'] at hbu
  have hbl : (s'.mem (State.addr (s'.gpr .r0 + BitVec.ofNat 32 (k + u)))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok (by omega) (by omega) s' (by rw [hkp.2.1, hkp.2.2.1, x']; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- The low `d` bits of `r3` into `r12`, and `r3` shifted right by `d`. -/
theorem extract_ok {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block (extract d)) s fun s' =>
      ((s'.gpr .r12).toNat = (s.gpr .r3).toNat % 2 ^ d ∧ (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ d ∧
        s'.mem = s.mem) ∧ Keep [.r3, .r12] s s' := by
  refine WP.keep _ ?_ rfl
  unfold extract
  run_block [show 1 ≤ 32 - d by omega, show 32 - d ≤ 31 by omega, hd1, show d ≤ 31 by omega, and_true]
  refine ⟨?_, by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 2 ^ 32 = 2 ^ d * 2 ^ (32 - d) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `r12` to
`r1 + 4j`, and writes only `r4` and `r12`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 →
    (s.gpr .r12).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (s.gpr .r12).toNat) ∧
        Keep [.r4, .r12] s s'

/-- Field `j`: the bytes it needs into `r3`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (hj : j < 8) {x : BitVec 32} (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 t)) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (State.addr (x + BitVec.ofNat 32 t))).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r3).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.r3, .r4, .r12] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  have hn8 : need d (j + 1) ≤ 20 := by unfold need; have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) (by omega) s h0 (fun u hu => hin _ (by omega))
    (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (extract_ok hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .r12).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have p₂ : s₂.gpr .r1 = s.gpr .r1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by omega) (by rw [k₂.2.2.1, k₁.2.2.1, p₂]; exact hout)
      (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, p₂, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, r₁, unpack_shift]

theorem unpackTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 nb) = true)
    (e₂ : encodable (BitVec.ofNat 32 (4 * c)) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 nb)), .dp .add .r1 .r1 (.imm (BitVec.ofNat 32 (4 * c))),
      .subs .r2 .r2 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 nb ∧ s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem) ∧
        Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `r0`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8)
    (e₁ : encodable (BitVec.ofNat 32 nb) = true) (e₂ : encodable (BitVec.ofNat 32 (4 * c)) = true) (s : State)
    (hx : (s.gpr .r0).toNat + nb ≤ 2 ^ 32) (hp : (s.gpr .r1).toNat + 4 * c ≤ 2 ^ 32)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), nb⟩ ⟨State.addr (s.gpr .r1), 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨State.addr (s.gpr .r1), 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 nb ∧ s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t =>
    (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) = H
  have ea : ∀ t < nb, State.addr (s.gpr .r0 + BitVec.ofNat 32 t) = State.addr (s.gpr .r0) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega)
  have ep : ∀ j < c, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega)
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  have p₁ : s₁.gpr .r1 = s.gpr .r1 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r3, .r4, .r12] s₁ s' ∧
      Frame [⟨State.addr (s.gpr .r1), 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j')) 32 =
        W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    have pj : s'.gpr .r1 = s.gpr .r1 := (hk.gpr (by decide)).trans p₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) (by omega) s' xj
      (fun t ht => by rw [ea t (by omega), hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin t (by omega))
      (fun t ht => by
        rw [ea t (by omega), hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep _ (Offset.contains_base _ (by omega) (by omega)))
      (by rw [pj, ep j hj, hk.2.2.1, k₁.2.2.1]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', pj, ep j hj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', pj, ep j hj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (unpackTail_ok e₁ e₂ s₂)
      fun s₃ ⟨⟨x₃, p₃, c₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [p₃, k₂.gpr (by decide), p₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.Arm.Pack
