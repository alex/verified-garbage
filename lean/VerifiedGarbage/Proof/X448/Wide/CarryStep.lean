import VerifiedGarbage.Proof.X448.Wide.UnpackRegs

/-! Untrusted: one wide carry step and its optional interface conversion. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

def encoded (v : Nat) (unpack : Bool) : Nat :=
  if unpack then v % VG.Proof.X448.radix + 2 ^ 64 * (v / VG.Proof.X448.radix) else v

theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hz : s.gpr .x11 = 0) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (carryStep o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / radix ∧ coeff t.mem base o i = encoded (v % radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  rw [carryStep, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadAt_ok hs (o := TMP) (k := i) (by simp only [TMP]; omega) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uz : u.gpr .x11 = 0 := (uk.1 _ (by decide)).trans hz
  have u9 : u.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) := (uk.1 _ (by decide)).trans hm
  have raw : pair (u.gpr .x4) (u.gpr .x5) + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (carryRegs_ok u uz u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have wkeep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    rw [ite_eq_right (by decide)]
    refine WP.mono (storeAt_ok ws (k := i) (by omega) ho8 .x4 .x11) fun t ⟨tm, tk⟩ => ?_
    have wz : w.gpr .x11 = 0 := (wk.1 _ (by decide)).trans uz
    refine ⟨?_, ?_, ?_, wkeep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl, wz]
      simp only [pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
        encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega)
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (storeAt_ok zs (k := i) (by omega) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, wkeep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl]
      simp only [pair, encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega)

end VG.Proof.X448.Wide
