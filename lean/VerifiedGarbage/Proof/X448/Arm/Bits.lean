import VerifiedGarbage.Proof.X448.Arm.BitBody
import VerifiedGarbage.Proof.X448.Arm.Clamp

/-!
# X448 on ARMv7: the scalar's decoded bits

Untrusted: everything here is checked by Lean. The loop expands all 56
bytes before applying the RFC 7748 scalar clamp.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  r1 : State.addr (s.gpr .r1) = k
  fit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
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
      WP isa (.loop (.block bitsBody) .ne) s fun s' => BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .ne)
    (Q := fun s' => BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.r1),
      (by rw [g' _ (by decide)]; exact hb.fit), b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z']
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
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => BInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : Keeps bitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
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

end VG.Proof.X448.Arm
