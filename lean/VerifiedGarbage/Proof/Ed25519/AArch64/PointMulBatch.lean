import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter

/-! Untrusted: one checkpoint batch advances the exact scalar-multiplication invariant. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.mem]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_counter {base : Addr} {o n : Nat} {s t : State} (h : CounterKeep base s t) :
    PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : env m' base = env m base := by
  funext i
  exact Outside_F h (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem TableFrame.bits {base : Addr} {m m' : Mem} (h : TableFrame base 5376 2048 m m')
    (i : Nat) (hi : i < 512) : m' (off base (768 + i)) = m (off base (768 + i)) := by
  apply h
  · rw [ofs_off' base (by omega)]; omega
  · rw [ofs_off' base (by omega)]; omega

theorem pointMulBatch_ok {s : State} {base : Addr} (hs : Scr s base)
    (j count scalar : Nat) (p : Spec.Ed25519.Point) (hj : j < count) (hn : count ≤ 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2))
    (ht : ∀ i < count, tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)) :
    WP isa pointMulBatch s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (16 * j) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧
      (∀ i < 16 * count, t.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) ∧
      (∀ i < count, tablePoint t.mem base (1280 + 128 * i) = powerPoint p (16 * i)) ∧
      PowersKeep base 56 7368 s t := by
  rw [pointMulBatch]
  refine WP.seq (WP.mono (batchBegin_ok hs j hc) fun a ⟨ac, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : PowersKeep base 56 7368 s a := ⟨fun r hr _ _ => ag r hr, ar, aw, asp,
    (TableFrame.table am).mono (by decide) (by decide)⟩
  have ae := header_env am
  refine WP.seq (WP.mono (prepareBatch_ok (ka.scratch hs) j (by omega) ac
    (by rw [ae]; exact hd)) fun b ⟨kb, bp, bt, bd⟩ => ?_)
  have bcounter : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 j := by
    exact ((tableFrame_outside kb.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans av
  have bbits : ∀ i < 16 * count, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.mem.bits i (by omega), am _ (by rw [ofs_off' base (by omega)]; omega), hb i hi]
  have bcheck : ∀ i < count, tablePoint b.mem base (1280 + 128 * i) = powerPoint p (16 * i) := by
    intro i hi
    rw [kb.mem.point (by omega) (Or.inl (by omega)) (by omega),
      (TableFrame.table am).point (by omega) (Or.inr (by omega)) (by omega), ht i hi]
  have btable : ∀ i < 16, tablePoint b.mem base (5376 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hi
    rw [bt i hi, (TableFrame.table am).point (by omega) (Or.inr (by omega)) (by omega), ht j hj, powerPoint_add]
  have bpoint : point (env b.mem base) 0 1 2 3 = after scalar p (16 * j + 16) := by
    rw [bp, ae, hp, Nat.mul_add, Nat.mul_one]
  have kab : PowersKeep base 56 7368 s b := ka.trans (kb.mono (by decide) (by decide))
  refine WP.seq (WP.mono (batchBitOffset_ok (kab.scratch hs) j (by omega) bcounter) fun c ⟨cs, kc⟩ => ?_)
  have kce : PowersKeep base 56 7368 b c := PowersKeep.of_keeps kc (by decide)
  have kabc := kab.trans kce
  refine WP.seq (WP.mono (accumulate16_ok (kabc.scratch hs) (16 * j) scalar p (by omega) cs
    (by intro i hi; rw [kc.mem]; exact bbits _ (by omega))
    (by rw [kc.mem]; exact bd) (by rw [kc.mem]; exact bpoint) (by rw [kc.mem]; exact btable))
    fun d ⟨dp, dd, kd⟩ => ?_)
  have dcounter : d.mem.readW (off base 56) 64 = BitVec.ofNat 64 j := by
    exact (kd.mem.word (d := 56) (Or.inl (by decide)) (by decide)).trans
      ((congrArg (fun m : Mem => m.readW (off base 56) 64) kc.mem).trans bcounter)
  have kabcd : PowersKeep base 56 7368 s d := kabc.trans (PowersKeep.of_counter kd)
  refine WP.mono (batchTest_ok (kabcd.scratch hs) j dcounter) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, tz, ?_, ?_, ?_, ?_, kabcd.trans (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact dcounter
  · rw [kt.mem]; exact dp
  · rw [kt.mem]; exact dd
  · intro i hi
    rw [kt.mem, kd.mem _ (by rw [ofs_off' base (by omega)]; omega), kc.mem]
    exact bbits i hi
  · intro i hi
    rw [kt.mem, workspace_tablePoint kd.mem (by omega) (by omega), kc.mem]
    exact bcheck i hi

end VG.Proof.Ed25519.AArch64
