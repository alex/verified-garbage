import VerifiedGarbage.Proof.X448.Wide.TailRegs
import VerifiedGarbage.Proof.X448.Wide.CarryStep

/-! Untrusted: narrow carry steps whose input coefficient already fits in one word. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Proof.X448.AArch64

theorem loadLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8)
    (hb : coeff s.mem base TMP i < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 16 * i)]) s fun t =>
      (t.gpr .x4).toNat = coeff s.mem base TMP i ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have al := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  have low := (pair_low64 _ _ hb).2
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨low, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block [st .x4 (TMP + 16 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 16 * i)) (s.gpr .x4) ∧ Keeps [] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have aw := hs.write (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.read, State.store, hs.x3, aw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (fun _ _ => rfl), rfl, rfl⟩

theorem tailStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (Impl.X448.AArch64.Tail.step o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / radix ∧ coeff t.mem base o i = encoded (v % radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  have hb' : coeff s.mem base TMP i < 2 ^ 64 := by omega
  have high := (pair_low64 _ _ hb').1
  rw [Impl.X448.AArch64.Tail.step, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadLow_ok hs hi hb') fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have u9 := (uk.1 .x9 (by decide)).trans hm
  have raw : (u.gpr .x4).toNat + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (tailRegs_ok u u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have keep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    have e := hfalse rfl
    subst o
    rw [ite_eq_right (by decide)]
    refine WP.mono (storeLow_ok ws hi) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm]
      have out := writeW_outside w.mem base (w.gpr .x4) (d := TMP + 16 * i) (by simp only [TMP]; omega)
      have lo : word (w.mem.writeW (off base (TMP + 16 * i)) (w.gpr .x4)) base (TMP + 16 * i) = w.gpr .x4 :=
        Mem.readW_writeW_self64 _ _ _
      have eh := out.word (d := TMP + 16 * i + 8) (Or.inr (by omega)) (by simp only [TMP]; omega)
      change pair (word _ base (TMP + 16 * i)) (word _ base (TMP + 16 * i + 8)) = _
      rw [lo, eh, wm, um]
      simp only [pair, high, Nat.mul_zero, Nat.add_zero, encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact (writeW_outside _ _ _ (by simp only [TMP]; omega)).mono (by omega) (by omega)
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (storeAt_ok zs (k := i) (by omega) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl]
      simp only [pair, encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega)

end VG.Proof.X448.Wide
