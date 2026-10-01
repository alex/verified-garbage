import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

/-!
# ML-DSA on AArch64: the butterflies of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. What one butterfly's code
stores (`bfly_ok`, `bflyInv_ok`), for any `len`, from the words it reads
and the zeta in `x6`; and that it does what the butterfly of the
specification does (`bfly_spec`, `bflyInv_spec`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## The values -/

/-- The sum of two values `x` and `y`, reduced. -/
theorem csubX_add64 {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a + b)).setWidth 32).toNat = (x + y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e : (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add]; omega
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_add']

/-- The difference of two values `x` and `y` (`x + q - y`), reduced. -/
theorem csubX_sub64 {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a + Qv - b)).setWidth 32).toNat = (x - y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e1 : (a + Qv).toNat = a.toNat + q := by
    rw [VG.Proof.MlKem.AArch64.toNat_add_n (by rw [toNat_Qv]; omega), toNat_Qv]
  have e : (a + Qv - b).toNat = a.toNat + q - b.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [e1, hb]; omega), e1]
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_sub, condSub_eq (by omega)]

/-- The difference, reduced, as a 64-bit value. -/
theorem csubX_sub64' {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (csubX (a + Qv - b)).toNat = (x - y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e1 : (a + Qv).toNat = a.toNat + q := by
    rw [VG.Proof.MlKem.AArch64.toNat_add_n (by rw [toNat_Qv]; omega), toNat_Qv]
  have e : (a + Qv - b).toNat = a.toNat + q - b.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [e1, hb]; omega), e1]
  rw [csubX_toNat (by rw [e, ha, hb]; omega), e, ha, hb, val_sub]

/-- The product of values `x` and `z`, reduced, as a 64-bit value. -/
theorem redX_mul64 {a b : BitVec 64} {x z : Zq} (ha : a.toNat = x.val) (hb : b.toNat = z.val) :
    (redX (a * b)).toNat = (x * z).val := by
  have hxz : x.val * z.val < q * q := Nat.mul_lt_mul_of_lt_of_lt x.isLt z.isLt
  have e : (a * b).toNat = x.val * z.val := by
    rw [BitVec.toNat_mul, ha, hb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hxz (by decide))
  rw [redX_toNat (by rw [e]; exact hxz), e, val_mul]

/-- A reduced 64-bit value, stored as a word. -/
theorem toNat_setWidth32_zq {a : BitVec 64} {x : Zq} (ha : a.toNat = x.val) : (a.setWidth 32).toNat = x.val := by
  have hx : x.val < 8380417 := x.isLt
  rw [toNat_setWidth32 (by rw [ha]; omega), ha]

/-! ## `NTT` -/

/-- The accesses of a butterfly on `[x2]` and `[x2 + 4len]`. -/
structure Acc (s : State) (len : Nat) : Prop where
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 4
  w0 : InRegions s.wr (s.gpr .x2) 4
  w1 : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 4
  off : 4 * len % 4 = 0 ∧ 4 * len < 16384

theorem bfly_ok (len : Nat) (s : State) (hc : Consts s) (ha : Acc s len) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.bfly len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (4 * len))
          ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) + Qv -
            redX (w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32) * s.gpr .x6))).setWidth 32)).writeW
          (s.gpr .x2) ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) +
            redX (w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32) * s.gpr .x6))).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold Impl.MlDsa.AArch64.Arith.bfly reduce Impl.MlKem.AArch64.csub
  arun [ha.r0, ha.r1, ha.w0, ha.w1, ha.off, hc.x9, hc.x10, hc.x11, redX, csubX]

/-! ## `NTT⁻¹` -/

theorem bflyInv_ok (len : Nat) (s : State) (hc : Consts s) (ha : Acc s len) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.bflyInv len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .x2) ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) +
          w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32))).setWidth 32)).writeW
          (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) ((redX (csubX (w64 (s.mem.readW (s.gpr .x2) 32) + Qv -
            w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32)) * s.gpr .x6)).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold Impl.MlDsa.AArch64.Arith.bflyInv reduce Impl.MlKem.AArch64.csub
  arun [ha.r0, ha.r1, ha.w0, ha.w1, ha.off, hc.x9, hc.x10, hc.x11, redX, csubX]

/-! ## What they do to a stored polynomial -/

/-- The code `code len` of a butterfly does what `op` does. -/
def BflyOk (code : Nat → List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ (fP : Addr) (len j : Nat), 0 < len → len ≤ 128 → j + len < 256 → ∀ (z : Zq) (F : Poly) (s : State),
    s.gpr .x2 = coeffAddr fP j → s.gpr .x6 = BitVec.ofNat 64 z.val → Consts s → PolyIs s.mem fP F →
    pR fP ∈ s.wr →
    WP isa (.block (code len)) s fun s' => (PolyIs s'.mem fP (op F j len z) ∧ Frame [pR fP] s.mem s'.mem ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s'

/-- The words a butterfly reads and writes. -/
theorem bfly_acc {fP : Addr} {len j : Nat} (hl : len ≤ 128) (hj : j + len < 256) {s : State}
    (hx2 : s.gpr .x2 = coeffAddr fP j) (hw : pR fP ∈ s.wr) : Acc s len := by
  have e : s.gpr .x2 + BitVec.ofNat 64 (4 * len) = coeffAddr fP (j + len) := by rw [hx2, coeffAddr_add]
  refine ⟨?_, ?_, ?_, ?_, ⟨by omega, by omega⟩⟩
  · rw [hx2]; exact ⟨_, List.mem_append_right _ hw, coeff_contains _ (show j < 256 by omega)⟩
  · rw [e]; exact ⟨_, List.mem_append_right _ hw, coeff_contains _ hj⟩
  · rw [hx2]; exact ⟨_, hw, coeff_contains _ (show j < 256 by omega)⟩
  · rw [e]; exact ⟨_, hw, coeff_contains _ hj⟩

/-- The two writes of a butterfly are within the polynomial. -/
theorem bfly_frame {fP : Addr} {len j : Nat} (hj : j + len < 256) (m : Mem) (a b : BitVec 32) :
    Frame [pR fP] m ((m.writeW (coeffAddr fP (j + len)) a).writeW (coeffAddr fP j) b) ∧
      Frame [pR fP] m ((m.writeW (coeffAddr fP j) a).writeW (coeffAddr fP (j + len)) b) :=
  ⟨(Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega)),
    (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)⟩

theorem bfly_spec : BflyOk Impl.MlDsa.AArch64.Arith.bfly Arith.bfly := by
  intro fP len j hlen hl hj z F s hx2 h6 hc hF hw
  have ha := bfly_acc hl hj hx2 hw
  refine WP.mono (bfly_ok len s hc ha) fun s' ⟨⟨hm, hx2', hx5⟩, hk⟩ => ⟨⟨?_, ?_, hx2', hx5⟩, hk⟩
  · rw [hm, h6, hx2, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    show PolyIs _ _ ((F.set! (j + len) (F[j]! - z * F[j + len]!)).set! j
      ((F.set! (j + len) (F[j]! - z * F[j + len]!))[j]! + z * F[j + len]!))
    rw [getElem!_set!_ne _ hj' (by omega)]
    have hT' : (redX (w64 (coeffAt s.mem fP (j + len)) * BitVec.ofNat 64 z.val)).toNat = (z * F[j + len]!).val := by
      rw [redX_mul64 (by rw [toNat_setWidth64]; exact polyIs_toNat hF hj)
        (BitVec.toNat_ofNat .. |>.trans (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le z.isLt (by decide)))), Fin.mul_comm]
    exact polyIs_writeW (polyIs_writeW hF hj _ (csubX_sub64 (by rw [toNat_setWidth64]; exact ha) hT')) hj' _
      (csubX_add64 (by rw [toNat_setWidth64]; exact ha) hT')
  · rw [hm, hx2, coeffAddr_add]
    exact (bfly_frame hj _ _ _).1

theorem bflyInv_spec : BflyOk Impl.MlDsa.AArch64.Arith.bflyInv Arith.bflyInv := by
  intro fP len j hlen hl hj z F s hx2 h6 hc hF hw
  have ha := bfly_acc hl hj hx2 hw
  refine WP.mono (bflyInv_ok len s hc ha) fun s' ⟨⟨hm, hx2', hx5⟩, hk⟩ => ⟨⟨?_, ?_, hx2', hx5⟩, hk⟩
  · rw [hm, h6, hx2, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hu := polyIs_toNat hF hj
    have hne : j ≠ j + len := by omega
    show PolyIs _ _ (((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
      (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!)).set! (j + len)
      (z * ((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
        (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!))[j + len]!))
    rw [getElem!_set!_ne _ hj hne, getElem!_set!_self _ hj]
    have e : ∀ (G : Poly) (x y : Zq), (G.set! (j + len) x).set! (j + len) y = G.set! (j + len) y := fun G x y =>
      ext_getElem! fun i hi => by
        by_cases h : i = j + len
        · subst h; rw [getElem!_set!_self _ hi, getElem!_set!_self _ hi]
        · rw [getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h)]
    rw [e]
    have hd := csubX_sub64' (x := F[j]!) (y := F[j + len]!) (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hu)
    have hT : ((redX (csubX (w64 (coeffAt s.mem fP j) + Qv - w64 (coeffAt s.mem fP (j + len))) *
        BitVec.ofNat 64 z.val)).setWidth 32).toNat = (z * (F[j]! - F[j + len]!)).val := by
      rw [toNat_setWidth32_zq (redX_mul64 hd
        (BitVec.toNat_ofNat .. |>.trans (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le z.isLt (by decide))))),
        Fin.mul_comm]
    exact polyIs_writeW (polyIs_writeW hF hj' _ (csubX_add64 (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hu))) hj _ hT
  · rw [hm, hx2, coeffAddr_add]
    exact (bfly_frame hj _ _ _).2

end VG.Proof.MlDsa.AArch64.Arith
