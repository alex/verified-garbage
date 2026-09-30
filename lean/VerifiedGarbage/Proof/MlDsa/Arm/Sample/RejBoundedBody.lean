import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedLoop

/-!
# ML-DSA on 32-bit ARM: an iteration of `vg_mldsa_rej_bounded_poly`

Untrusted: everything here is checked by Lean. An iteration from `Base`
with the coefficients `L`: the byte `z` of the XOF output loaded, its low
half-byte in `r9` and `Z` set iff `j ≥ 256` (`load_ok`, leaving `LD`); if
`j < 256`, the low half-byte tried (`try_ok`), the high half-byte and the
test of `j ≥ 256` again (`hi_ok`, leaving `HI`), and the high half-byte
tried if `j < 256` (`mid_ok`); then the step (`stepB_ok`): what `rbStep`
does (`body_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored ifT ifF hbTry_length halfByteOk_le rbFold_snoc
  rbFold_length_le)
open VG.Spec.MlDsa (Zq)
open VG.Spec.Sha3 (bytesAt)

/-- The low half-byte of a byte, as `rbLoad` computes it. -/
theorem lo_eq (z : Byte) : BitVec.setWidth 32 z <<< 28 >>> 28 = BitVec.ofNat 32 (z.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The high half-byte of a byte, as `rbHi` computes it. -/
theorem hi_eq (z : Byte) : BitVec.setWidth 32 z >>> 4 = BitVec.ofNat 32 (z.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- After the loads: the byte `z` in `r8`, its low half-byte in `r9`, and `Z`
set iff `j ≥ 256`. -/
structure LD (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  base : Base P σ X t L s
  r8 : s.gpr .r8 = BitVec.setWidth 32 (zAt X t)
  r9 : s.gpr .r9 = BitVec.ofNat 32 ((zAt X t).toNat % 16)
  z : s.z = decide (256 ≤ L.length)

/-- After the high half-byte: in `r9`, and `Z` set iff `j ≥ 256`. -/
structure HI (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  base : Base P σ X t L s
  r8 : s.gpr .r8 = BitVec.setWidth 32 (zAt X t)
  r9 : s.gpr .r9 = BitVec.ofNat 32 ((zAt X t).toNat / 16)
  z : s.z = decide (256 ≤ L.length)

theorem lt31 {L : List Zq} (h : L.length ≤ 256) : L.length < 2 ^ 31 := by omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem ld3_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : Base P σ X t L s) :
    WP isa (.block [.ldrb .r8 .r0 0, .mov .r9 (.shifted .r8 .lsl 28), .mov .r9 (.shifted .r9 .lsr 28)]) s
      fun s' => s'.gpr .r8 = BitVec.setWidth 32 (zAt X t) ∧ s'.gpr .r9 = BitVec.ofNat 32 ((zAt X t).toNat % 16) ∧
        (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = P.at' 840 + BitVec.ofNat 64 t := by
    rw [h.r0]
    show State.addr (P.scr + BitVec.ofNat 32 (840 + t) + 0#32) = _
    rw [BitVec.add_zero, at_eq hp (by omega), Offset.add_add]
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) 1 := by
    rw [ea, Offset.add_add]; exact inScrRd hp h.env (by omega)
  have hz : s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) = zAt X t := by
    have := MlKem.bytesAt_getD s.mem (P.at' 840) (len := 544) (i := t) (by omega)
    rw [h.out] at this
    rw [ea, ← this]
  have h0 : (0 : Nat) < 4096 := by decide
  run_block [hin, hz, h0, lo_eq, and_true]
  refine ⟨trivial, trivial, fun r h8 h9 => ?_⟩
  simp [h8, h9]

/-- The loads. -/
theorem load_ok {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State} (h : Base P σ X t L s) :
    WP isa (.block rbLoad) s (LD P σ X t L) := by
  unfold rbLoad
  rw [WP.block_append_iff]
  refine WP.mono (ld3_ok hp ht h) fun s1 ⟨h8, h9, hg, hm, hrd, hwr, hsp⟩ => ?_
  have b1 : Base P σ X t L s1 := h.regs (fun r h8 h9 _ _ => hg r h8 h9) hm hrd hwr hsp
  refine WP.mono (jFull_ok s1 b1.r2 (lt31 b1.len)) fun s2 ⟨hz, hg2, hm2, hrd2, hwr2, hsp2⟩ =>
    ⟨b1.regs (fun r _ _ _ h11 => hg2 r h11) hm2 hrd2 hwr2 hsp2, ?_, ?_, hz⟩
  · rw [hg2 .r8 (by decide), h8]
  · rw [hg2 .r9 (by decide), h9]

end

/-- The high half-byte, from the byte in `r8`. -/
theorem hi_ok {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq} {s : State} (h : Base P σ X t L s)
    (h8 : s.gpr .r8 = BitVec.setWidth 32 (zAt X t)) : WP isa (.block rbHi) s (HI P σ X t L) := by
  unfold rbHi
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r9 (BitVec.ofNat 32 ((zAt X t).toNat / 16))) (by
    run_block [h8, hi_eq]) fun s1 e1 => ?_
  subst e1
  have b1 : Base P σ X t L (s.setReg .r9 (BitVec.ofNat 32 ((zAt X t).toNat / 16))) :=
    h.regs (fun r _ h9 _ _ => RegUpd.gpr_setReg_of_ne _ _ h9) rfl rfl rfl rfl
  refine WP.mono (jFull_ok _ b1.r2 (lt31 b1.len)) fun s2 ⟨hz, hg2, hm2, hrd2, hwr2, hsp2⟩ =>
    ⟨b1.regs (fun r _ _ _ h11 => hg2 r h11) hm2 hrd2 hwr2 hsp2, ?_, ?_, hz⟩
  · rw [hg2 .r8 (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), h8]
  · rw [hg2 .r9 (by decide), RegUpd.gpr_setReg_self]

/-- The coefficients after an iteration's tries, from the byte `z`. -/
theorem rbStep_eq (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = if L.length < 256 then
      (if (hbTry η L (z.toNat % 16)).length < 256 then hbTry η (hbTry η L (z.toNat % 16)) (z.toNat / 16)
        else hbTry η L (z.toNat % 16)) else L := rfl

theorem hbTry_length_le {η : Nat} {L : List Zq} (hL : L.length < 256) (b : Nat) : (hbTry η L b).length ≤ 256 := by
  rw [hbTry_length]; have := halfByteOk_le η b; omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The tries of an iteration, from the loads. -/
theorem mid_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {s : State}
    (h : LD P σ X t L s) :
    WP isa (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η))))) s
      (Base P σ X t (rbStep η L (zAt X t))) := by
  rw [rbStep_eq]
  refine WP.ite (decide (256 ≤ L.length)) (by show some s.z = _; rw [h.z]) (fun hr => ?_) (fun hr => ?_)
  · simp only [decide_eq_true_eq] at hr
    rw [ifF (by omega)]
    exact WP.block_nil h.base
  simp only [decide_eq_false_iff_not] at hr
  rw [ifT (by omega)]
  refine WP.seq (WP.mono (try_ok hp hη (Nat.mod_lt _ (by decide)) h.base (by omega) h.r9) fun s1 ⟨b1, e8⟩ => ?_)
  refine WP.seq (WP.mono (hi_ok b1 (by rw [e8, h.r8])) fun s2 h2 => ?_)
  refine WP.ite (decide (256 ≤ (hbTry η L ((zAt X t).toNat % 16)).length)) (by show some s2.z = _; rw [h2.z])
    (fun hr' => ?_) (fun hr' => ?_)
  · simp only [decide_eq_true_eq] at hr'
    rw [ifF (by omega)]
    exact WP.block_nil h2.base
  · simp only [decide_eq_false_iff_not] at hr'
    rw [ifT (by omega)]
    exact WP.mono (try_ok hp hη (by have := (zAt X t).isLt; omega) h2.base (by omega) h2.r9) fun _ h => h.1

end

theorem ofNat_pred {k : Nat} (hk : 0 < k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, Nat.mod_eq_of_lt hk']
  omega

/-- The step, to iteration `t + 1`: `Z` set iff it is the last. -/
theorem stepB_ok {P : Sp} {σ : State} {X : List Byte} {t : Nat} (ht : t < 544) {L : List Zq} {s : State}
    (h : Base P σ X t L s) :
    WP isa (.block (step 1)) s fun s' => Base P σ X (t + 1) L s' ∧ s'.z = decide (t + 1 = 544) := by
  refine WP.mono (step_ok s (k := 1) (by decide)) fun s' ⟨h0, h3, hz, hg, hm, hrd, hwr, hsp⟩ => ?_
  have e3 : BitVec.ofNat 32 (544 - t) - 1 = BitVec.ofNat 32 (544 - (t + 1)) := by
    rw [ofNat_pred (by omega) (by omega)]; rfl
  refine ⟨⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide)).trans h.env.r5, (hg .r6 (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
    by rw [hm]; exact h.out, by rw [h0, h.r0]; exact Offset.add_add_eq _ (by omega), by rw [h3, h.r3, e3],
    by rw [hg .r2 (by decide) (by decide)]; exact h.r2, h.len, by rw [hm]; exact h.st⟩, ?_⟩
  have ez := count_z (N := 544) (i := t) (k := 1) ht (by decide) (by decide)
  simp only [Nat.one_mul] at ez
  rw [hz, h.r3]; exact ez

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} (hX : X.length = 544) {t : Nat} (ht : t < 544) :
    Lf η X (t + 1) = rbStep η (Lf η X t) (zAt X t) := by
  simp only [Lf]
  rw [take_succ' _ (by omega), rbFold_snoc]

theorem Lf_length_le (η : Nat) (X : List Byte) (t : Nat) : (Lf η X t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {P : Sp} {σ : State} (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    (hX : X.length = 544) {t : Nat} (ht : t < 544) {s : State} (h : Base P σ X t (Lf η X t) s) :
    WP isa (rbBody η) s fun s' => Base P σ X (t + 1) (Lf η X (t + 1)) s' ∧ s'.z = decide (t + 1 = 544) := by
  rw [Lf_succ η hX ht]
  exact WP.seq (WP.mono (load_ok hp ht h) fun _ h1 =>
    WP.seq (WP.mono (mid_ok hp hη h1) fun _ h2 => stepB_ok ht h2))

end VG.Proof.MlDsa.Arm.Sample.RejBounded
