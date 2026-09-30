import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttBfly

/-!
# ML-DSA on AArch64: the blocks and layers of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. The loops of `nttBlk` and
`nttLay`, for any butterfly code that does what a butterfly `op` of the
specification does (`BflyOk`): a block runs `len` butterflies (`blockN`),
and a layer its `128 / len` blocks (`layerN`), with the zetas `Z (zi c)`,
whose values `tab` the table at `zP` holds.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

/-- Where the zeta pointer moves: up or down by 4 bytes. -/
def zstep (up : Bool) (a : Addr) : Addr := if up then a + BitVec.ofNat 64 4 else a - BitVec.ofNat 64 4

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : BflyOk code op)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {fP : Addr} {len start : Nat} (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256)
    (z : Zq) (G : Poly) (s : State) (hx2 : s.gpr .x2 = coeffAddr fP start)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 z.val) (hc : Consts s) (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block (code len)) (.nonzero .x .x5)) s fun s' =>
      PolyIs s'.mem fP (blockN op G len z start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + len) ∧ Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine wp_countdown (cnt := .x5) (N := len) (by omega) hlen (fun t s' =>
      PolyIs s'.mem fP (blockN op G len z start t) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + t) ∧ Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s')
    (fun t ht s' ⟨hP, hf, hs', hk⟩ _ => ?_) ⟨hG, Frame.refl _ _, hx2, Keep.refl _ _⟩ h5
  refine WP.mono (hb fP len (start + t) hlen hl (by omega) z _ s' hs' (by rw [hk.get .x6, h6])
    ⟨by rw [hk.get .x9, hc.x9], by rw [hk.get .x10, hc.x10], by rw [hk.get .x11, hc.x11]⟩ hP
    (by rw [hk.wr]; exact hw)) fun s'' ⟨⟨hP', hf', hx2', hx5⟩, hk'⟩ =>
      ⟨⟨?_, hf.trans hf', by rw [hx2', hs', coeffAddr_next, Nat.add_assoc], (hk.trans hk').mono⟩, hx5⟩
  rw [blockN_succ]; exact hP'

omit hb in
theorem blkPre_ok (len : Nat) (up : Bool) (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .x3) 4) :
    WP isa (.block [.ldr .w .x6 .x3 0, if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4,
      .movz .x .x5 (BitVec.ofNat 16 len) 0]) s fun s' =>
      (s'.gpr .x6 = w64 (s.mem.readW (s.gpr .x3) 32) ∧ s'.gpr .x3 = zstep up (s.gpr .x3) ∧
        s'.gpr .x5 = (BitVec.ofNat 16 len).setWidth 64 ∧ s'.mem = s.mem) ∧ Keep [.x6, .x3, .x5] s s' := by
  cases up
  · refine WP.keep _ ?_ (by rfl)
    arun [h, zstep]
  · refine WP.keep _ ?_ (by rfl)
    arun [h, zstep]

omit hb in
theorem blkPost_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 (4 * len), .subImm .x .x4 .x4 1]) s fun s' =>
      (s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (4 * len) ∧ s'.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 1 ∧
        s'.mem = s.mem) ∧ Keep [.x2, .x4] s s' := by
  have h : 4 * len < 4096 := by omega
  refine WP.keep _ ?_ (by rfl)
  arun [h]

/-- A block, with the zeta `Z k` at `x3`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {fP zP : Addr} {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256)
    (hk : k < 256) (up : Bool) (G : Poly) (s : State) (hx2 : s.gpr .x2 = coeffAddr fP start)
    (h3 : s.gpr .x3 = coeffAddr zP k) (hc : Consts s) (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : pR zP ∈ s.rd ++ s.wr) (ht : Tab tab s.mem zP 256) :
    WP isa (nttBlk (code len) len up) s fun s' =>
      (PolyIs s'.mem fP (blockN op G len (Z k) start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + 2 * len) ∧ s'.gpr .x3 = zstep up (s.gpr .x3) ∧
        s'.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 1) ∧
      Keep [.x6, .x3, .x5, .x2, .x5, .x12, .x13, .x14, .x15, .x2, .x4] s s' := by
  refine WP.seq (WP.mono (blkPre_ok len up s (by rw [h3]; exact ⟨_, hz, coeff_contains _ hk⟩))
    fun s1 ⟨⟨h6, h3', h5, hm⟩, k1⟩ => ?_)
  have hz6 : s1.gpr .x6 = BitVec.ofNat 64 (Z k).val := by
    rw [h6, h3, ← coeffAt_eq, ht k hk, ← hZ k hk]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (Z k).isLt
    rw [hZ k hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (by decide))]
  refine WP.seq (WP.mono (bflys_ok hb (fP := fP) hlen hl hs (Z k) G s1 (by rw [k1.get .x2, hx2]) hz6
    ⟨by rw [k1.get .x9, hc.x9], by rw [k1.get .x10, hc.x10], by rw [k1.get .x11, hc.x11]⟩
    (by rw [hm]; exact hG) (by rw [k1.wr]; exact hw) (by rw [h5]; exact imm16 (by omega)))
    fun s2 ⟨hP, hf, hx22, k2⟩ => ?_)
  refine WP.mono (blkPost_ok len hl s2) fun s3 ⟨⟨hx23, hx4, hm3⟩, k3⟩ =>
    ⟨⟨by rw [hm3]; exact hP, by rw [hm3, ← hm]; exact hf, ?_, ?_, ?_⟩, ((k1.trans k2).trans k3).mono⟩
  · rw [hx23, hx22, coeffAddr_add, show start + len + len = start + 2 * len by omega]
  · rw [k3.get .x3, k2.get .x3, h3']
  · rw [hx4, k2.get .x4, k1.get .x4]

/-! ## A layer -/

omit hb in
theorem layPre_ok (c : Nat) (hc : c < 65536) (s : State) :
    WP isa (.block [.movz .x .x4 (BitVec.ofNat 16 c) 0]) s fun s' =>
      (s'.gpr .x4 = BitVec.ofNat 64 c ∧ s'.mem = s.mem) ∧ Keep [.x4] s s' := by
  refine WP.keep _ ?_ (by rfl)
  arun [imm16 hc]

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.subImm .x .x2 .x2 1024]) s fun s' =>
      (s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1024 ∧ s'.mem = s.mem) ∧ Keep [.x2] s s' := by
  refine WP.keep _ ?_ (by rfl)
  arun

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len := by
  decide

/-- A layer, from `x2` = `f` and the zeta of its first block at `x3`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {fP zP : Addr} {len : Nat}
    (hlen : len ∈ nttLens) (up : Bool) (zi : Nat → Nat)
    (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, zstep up (coeffAddr zP (zi c)) = coeffAddr zP (zi (c + 1)))
    (F : Poly) (s : State) (hx2 : s.gpr .x2 = fP) (h3 : s.gpr .x3 = coeffAddr zP (zi 0)) (hc : Consts s)
    (hF : PolyIs s.mem fP F) (hw : pR fP ∈ s.wr) (hz : pR zP ∈ s.rd ++ s.wr)
    (hd : (pR zP).Disjoint (pR fP)) (ht : Tab tab s.mem zP 256) :
    WP isa (nttLay (code len) len up) s fun s' =>
      (PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = fP ∧ s'.gpr .x3 = coeffAddr zP (zi (128 / len))) ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3⟩ := lens_facts len hlen
  have h128 : 128 / len ≤ 128 := Nat.div_le_self 128 len
  refine WP.seq (WP.mono (layPre_ok (128 / len) (by omega) s) fun s1 ⟨⟨hx4, hm⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
      Frame [pR fP] s.mem s'.mem ∧ s'.gpr .x2 = coeffAddr fP 256 ∧
      s'.gpr .x3 = coeffAddr zP (zi (128 / len)) ∧ Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s') ?_
    fun s2 ⟨hP, hf, hx22, h32, k2⟩ => ?_)
  · refine WP.mono (wp_countdown (cnt := .x4) (N := 128 / len) (Nat.lt_of_le_of_lt h128 (by decide)) hl3
      (fun c (s' : State) =>
        PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) c) ∧ Frame [pR fP] s.mem s'.mem ∧
          s'.gpr .x2 = coeffAddr fP (2 * len * c) ∧ s'.gpr .x3 = coeffAddr zP (zi c) ∧
          Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s')
      (fun c hc' s' ⟨hP, hf, hs', h3', hk⟩ _ => ?_)
      ⟨by rw [hm]; exact hF, by rw [hm]; exact Frame.refl _ _,
        by rw [k1.get .x2, hx2, coeffAddr, Nat.mul_zero, Nat.mul_zero, BitVec.add_zero],
        by rw [k1.get .x3, h3], k1.mono⟩ hx4)
      fun s' ⟨hP, hf, hs', h3', hk⟩ => ⟨hP, hf, by rw [hs', hl2], h3', hk⟩
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    refine WP.mono (blk_ok hb hZ hl0 hl1 hcm (hzi c hc') up _ s' hs' h3'
      ⟨by rw [hk.get .x9, hc.x9], by rw [hk.get .x10, hc.x10], by rw [hk.get .x11, hc.x11]⟩ hP
      (by rw [hk.wr]; exact hw) (by rw [hk.rd, hk.wr]; exact hz) (ht.frame hf (by simpa using hd) (by decide)))
      fun s'' ⟨⟨hP', hf', hx2', h3'', hx4'⟩, hk'⟩ => ⟨⟨by rw [layerN_succ]; exact hP',
        hf.trans hf', ?_, ?_, (hk.trans hk').mono⟩, hx4'⟩
    · rw [hx2', Nat.mul_succ]
    · rw [h3'', h3', hstep c hc']
  · refine WP.mono (layPost_ok s2) fun s3 ⟨⟨hx23, hm3⟩, k3⟩ =>
      ⟨⟨by rw [hm3]; exact hP, by rw [hm3]; exact hf, ?_, by rw [k3.get .x3, h32]⟩,
        (k2.trans k3).mono⟩
    rw [hx23, hx22, coeffAddr]
    exact BitVec.add_sub_cancel _ _

end

end VG.Proof.MlDsa.AArch64.Arith
