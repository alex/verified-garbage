import VerifiedGarbage.Proof.X448.AArch64.BitBody
import VerifiedGarbage.Proof.X448.AArch64.Clamp

/-!
# X448 on AArch64: the scalar's decoded bits

Untrusted: everything here is checked by Lean. The loop expands all 56
bytes before applying the RFC 7748 scalar clamp.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.lt_or_ge (i + 1) 56 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 56), Bool.not_false],
      56 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 55 := by omega
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 448`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      Outside.refl _ _ _ _, fun t ht => absurd ht (by omega)⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (clamp_ok h₂.scr) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact h₂.gpr r hr
  · rw [m₃, clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [m₃, clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [writeW8_apply, off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [h₂.bits t (by omega), getD_bytesAt _ _ (by omega)]

end VG.Proof.X448.AArch64
