import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttBfly
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table

/-!
# ML-DSA on x86-64: the blocks and layers of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. The loops of `nttBlk` and
`nttLay`, for any butterfly code that does what a butterfly `op` of the
specification does (`BflyOk`): a block runs `len` butterflies (`blockN`),
and a layer its `128 / len` blocks (`layerN`), with the zetas `Z (zi c)`,
whose values `tab` the table at `zP` holds.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep wp_countdown toNat_setWidth64)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : BflyOk code op)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {fP : Addr} {len start : Nat} (hlen : 0 < len) (hs : start + 2 * len ≤ 256) (z : Zq)
    (G : Poly) (s : State) (hsi : s.gpr .rsi = coeffAddr fP start) (h9 : s.gpr .r9 = BitVec.ofNat 64 z.val)
    (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr) (hc : s.gpr .rcx = BitVec.ofNat 64 len) :
    WP isa (.loop (.block (code len)) .ne) s fun s' =>
      PolyIs s'.mem fP (blockN op G len z start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .rsi = coeffAddr fP (start + len) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  refine wp_countdown (cnt := .rcx) (N := len) (by omega) hlen (fun t s' =>
      PolyIs s'.mem fP (blockN op G len z start t) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .rsi = coeffAddr fP (start + t) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s')
    (fun t ht s' ⟨hP, hf, hs', hk⟩ _ => ?_) (fun _ h => h) ⟨hG, Frame.refl _ _, hsi, Keep.refl _ _⟩ hc
  refine WP.mono (hb fP len (start + t) hlen (by omega) z _ s' hs' (by rw [hk.gpr (by decide), h9]) hP
    (by rw [hk.2.2]; exact hw)) fun s'' ⟨⟨hP', hf', hsi', hcx, hz⟩, hk'⟩ =>
      ⟨⟨?_, hf.trans hf', by rw [hsi', hs', coeffAddr_succ, Nat.add_assoc], (hk.trans hk').mono (by decide)⟩,
        hcx, hz⟩
  rw [blockN_succ]; exact hP'

omit hb in
theorem blkPre_ok (len : Nat) (dz : BitVec 32) (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4) :
    WP isa (.block [.mov32 .r9 (.mem (at_ .r8 0)), .alu .add .r8 (.imm dz),
      .mov32 .rcx (.imm (BitVec.ofNat 32 len))]) s fun s' =>
      (s'.gpr .r9 = BitVec.setWidth 64 (s.mem.readW (s.gpr .r8) 32) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
        s'.gpr .rcx = BitVec.setWidth 64 (BitVec.ofNat 32 len) ∧ s'.mem = s.mem) ∧ Keep [.r9, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrund [h]

omit hb in
theorem blkPost_ok (len : Nat) (hl : 4 * len < 2 ^ 31) (s : State) :
    WP isa (.block [.alu .add .rsi (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rdi (.imm 1)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (4 * len) ∧ s'.gpr .rdi = s.gpr .rdi - 1 ∧
        s'.zf = some (s.gpr .rdi - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rsi, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrund [sx_ofNat hl]

/-- A block, with the zeta `Z k` at `r8`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {fP zP : Addr} {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256)
    (hk : k < 256) (dz : BitVec 32) (G : Poly) (s : State) (hsi : s.gpr .rsi = coeffAddr fP start)
    (h8 : s.gpr .r8 = coeffAddr zP k) (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : pR zP ∈ s.rd ++ s.wr) (ht : Tab tab s.mem zP 256) :
    WP isa (nttBlk (code len) len dz) s fun s' =>
      (PolyIs s'.mem fP (blockN op G len (Z k) start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .rsi = coeffAddr fP (start + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
        s'.gpr .rdi = s.gpr .rdi - 1 ∧ s'.zf = some (s.gpr .rdi - 1 == 0)) ∧
      Keep [.r9, .r8, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11, .rsi, .rdi] s s' := by
  refine WP.seq (WP.mono (blkPre_ok len dz s (by rw [h8]; exact ⟨_, hz, coeff_contains _ (show k < 256 by omega)⟩))
    fun s1 ⟨⟨h9, h8', hc, hm⟩, k1⟩ => ?_)
  have hz9 : s1.gpr .r9 = BitVec.ofNat 64 (Z k).val := by
    rw [h9, h8, ← coeffAt_eq, ht k hk, ← hZ k hk]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := val_lt (Z k)
    rw [hZ k hk, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.seq (WP.mono (bflys_ok hb (fP := fP) hlen hs (Z k) G s1 (by rw [k1.gpr (by decide), hsi]) hz9
    (by rw [hm]; exact hG) (by rw [k1.2.2]; exact hw) (by
      rw [hc]; apply BitVec.eq_of_toNat_eq
      rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)) fun s2 ⟨hP, hf, hsi2, k2⟩ => ?_)
  refine WP.mono (blkPost_ok len (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 4 hl) (by decide)) s2)
    fun s3 ⟨⟨hsi3, hdi, hz3, hm3⟩, k3⟩ =>
    ⟨⟨by rw [hm3]; exact hP, by rw [hm3, ← hm]; exact hf, ?_, ?_, ?_, ?_⟩, ((k1.trans k2).trans k3).mono (by decide)⟩
  · rw [hsi3, hsi2, coeffAddr_add, show start + len + len = start + 2 * len by omega]
  · rw [k3.gpr (by decide), k2.gpr (by decide), h8']
  · rw [hdi, k2.gpr (by decide), k1.gpr (by decide)]
  · rw [hz3, k2.gpr (by decide), k1.gpr (by decide)]

/-! ## A layer -/

omit hb in
theorem layPre_ok (c : Nat) (hl : c < 2 ^ 31) (s : State) :
    WP isa (.block [.mov32 .rdi (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      (s'.gpr .rdi = BitVec.ofNat 64 c ∧ s'.mem = s.mem) ∧ Keep [.rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrund
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.alu .sub .rsi (.imm 1024)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi - 1024 ∧ s'.mem = s.mem) ∧ Keep [.rsi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrund [show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 by decide]

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len := by
  decide

/-- A layer, from `rsi` = `f` and the zeta of its first block at `r8`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {fP zP : Addr} {len : Nat}
    (hlen : len ∈ nttLens) (dz : BitVec 32) (zi : Nat → Nat)
    (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, coeffAddr zP (zi c) + BitVec.signExtend 64 dz = coeffAddr zP (zi (c + 1)))
    (F : Poly) (s : State) (hsi : s.gpr .rsi = fP) (h8 : s.gpr .r8 = coeffAddr zP (zi 0))
    (hF : PolyIs s.mem fP F) (hw : pR fP ∈ s.wr) (hz : pR zP ∈ s.rd ++ s.wr)
    (hd : (pR zP).Disjoint (pR fP)) (ht : Tab tab s.mem zP 256) :
    WP isa (nttLay (code len) len dz) s fun s' =>
      (PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .rsi = fP ∧ s'.gpr .r8 = coeffAddr zP (zi (128 / len))) ∧
      Keep [.rdi, .r9, .r8, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11, .rsi, .rdi, .rsi] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3⟩ := lens_facts len hlen
  refine WP.seq (WP.mono (layPre_ok (128 / len) (by have := Nat.div_le_self 128 len; omega) s)
    fun s1 ⟨⟨hdi, hm⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
      Frame [pR fP] s.mem s'.mem ∧ s'.gpr .rsi = coeffAddr fP 256 ∧ s'.gpr .r8 = coeffAddr zP (zi (128 / len)) ∧
      Keep [.rdi, .r9, .r8, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11, .rsi, .rdi] s s') ?_
    fun s2 ⟨hP, hf, hsi2, h82, k2⟩ => ?_)
  · refine wp_countdown (cnt := .rdi) (N := 128 / len) (by have := Nat.div_le_self 128 len; omega) hl3
      (fun c (s' : State) =>
        PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) c) ∧ Frame [pR fP] s.mem s'.mem ∧
          s'.gpr .rsi = coeffAddr fP (2 * len * c) ∧ s'.gpr .r8 = coeffAddr zP (zi c) ∧
          Keep [.rdi, .r9, .r8, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11, .rsi, .rdi] s s')
      (fun c hc s' ⟨hP, hf, hs', h8', hk⟩ _ => ?_)
      (fun s' ⟨hP, hf, hs', h8', hk⟩ => ⟨hP, hf, by rw [hs', hl2], h8', hk⟩)
      ⟨by rw [hm]; exact hF, by rw [hm]; exact Frame.refl _ _, by rw [k1.gpr (by decide), hsi]; simp,
        by rw [k1.gpr (by decide), h8], k1.mono (by decide)⟩ hdi
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    refine WP.mono (blk_ok hb hZ hl0 hl1 hcm (hzi c hc) dz _ s' hs' h8' hP (by rw [hk.2.2]; exact hw)
      (by rw [hk.2.1, hk.2.2]; exact hz) (ht.frame hf (by simpa using hd) (by decide)))
      fun s'' ⟨⟨hP', hf', hsi', h8'', hdi', hz'⟩, hk'⟩ => ⟨⟨by rw [layerN_succ]; exact hP',
        hf.trans hf', ?_, ?_, (hk.trans hk').mono (by decide)⟩, hdi', hz'⟩
    · rw [hsi', Nat.mul_succ]
    · rw [h8'', h8', hstep c hc]
  · refine WP.mono (layPost_ok s2) fun s3 ⟨⟨hsi3, hm3⟩, k3⟩ =>
      ⟨⟨by rw [hm3]; exact hP, by rw [hm3]; exact hf, ?_, by rw [k3.gpr (by decide), h82]⟩,
        (k2.trans k3).mono (by decide)⟩
    rw [hsi3, hsi2, coeffAddr]
    show fP + BitVec.ofNat 64 1024 - 1024 = fP
    exact BitVec.add_sub_cancel _ _

end

end VG.Proof.MlDsa.X86_64.Arith
