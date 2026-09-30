import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulLoop

/-! Untrusted: checkpoint generation and batch descent implement pointMul. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scr s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  rw [mulCounterInit, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 (BitVec.ofNat 64 count)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc (hs.of_keeps ka (by decide)) (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ka.gpr r (by simpa only [List.mem_singleton] using hr), ka.rd, ka.wr, ka.sp, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact av
  · rw [ka.mem]; exact writeW_outside _ _ _ (by decide)

theorem pointMultiplyInit_ok {s : State} {base : Addr} (hs : Scr s base)
    (count scalar : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (pointMultiplyInit count) s fun t =>
      PointMulInv s base count scalar (point (env s.mem base) 0 1 2 3) count t := by
  rw [pointMultiplyInit]
  refine WP.seq (WP.mono (pointPowers_ok true hs 1280 count (by decide) (by omega) hn0 hn hd)
    fun a ⟨atab, _, ahigh, ka⟩ => ?_)
  have ad : env a.mem base 16 = Spec.Ed25519.d := (ahigh 16 (by decide)).trans hd
  have abits : ∀ i < 16 * count, a.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [ka.mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), hb i hi]
  have kat : PowersKeep base 56 7368 s a := ka.mono (by decide) (by omega)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (ka.scratch hs))
    fun b ⟨kb, vb⟩ => ?_)
  have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [vb]; exact ad
  have bp : point (env b.mem base) 0 1 2 3 =
      after scalar (point (env s.mem base) 0 1 2 3) (16 * count) := by
    rw [vb, constPoint_eval, after_top _ _ _ hscalar]
  have bbits : ∀ i < 16 * count, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega), abits i hi]
  have btab : ∀ i < count, tablePoint b.mem base (1280 + 128 * i) =
      powerPoint (point (env s.mem base) 0 1 2 3) (16 * i) := by
    intro i hi
    rw [workspace_tablePoint kb.mem (by omega) (by omega)]
    exact atab i hi
  have kab := kat.trans (PowersKeep.of_keep kb)
  refine WP.mono (mulCounterInit_ok (kab.scratch hs) count) fun c ⟨cc, cg, cr, cw, csp, cm⟩ => ?_
  have kc : PowersKeep base 56 7368 b c := ⟨fun r _ _ hr => cg r (by
    intro he; subst r; exact hr (by decide)), cr, cw, csp, (TableFrame.table cm).mono (by decide) (by decide)⟩
  have ce := header_env cm
  exact ⟨hn0, Nat.le_refl _, (kab.trans kc).scratch hs, cc,
    (by rw [ce]; exact bd), (by rw [ce]; exact bp),
    (by intro i hi; rw [cm _ (by rw [ofs_off' base (by omega)]; omega)]; exact bbits i hi),
    (by intro i hi; rw [(TableFrame.table cm).point (by omega) (Or.inr (by omega)) (by omega)]; exact btab i hi),
    kab.trans kc⟩

theorem pointMultiply_ok {s : State} {base : Addr} (hs : Scr s base)
    (count scalar : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (pointMultiply count) s fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar (point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s t := by
  rw [pointMultiply]
  refine WP.seq (WP.mono (pointMultiplyInit_ok hs count scalar hn0 hn hscalar hd hb) fun a h => ?_)
  refine WP.mono (pointMulLoop_ok h.scratch count scalar _ hn0 hn h.counter h.d h.value h.bits h.table)
    fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨tv, td, h.keep.trans kt⟩

end VG.Proof.Ed25519.AArch64
