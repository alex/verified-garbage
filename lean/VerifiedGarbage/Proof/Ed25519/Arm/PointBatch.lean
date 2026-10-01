import VerifiedGarbage.Impl.Ed25519.Arm.PointBatch
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateLoop
import VerifiedGarbage.Proof.Ed25519.Arm.PointPowersLoop

/-! Untrusted: the local table preserves the accumulator and the checkpoint table. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.of_acc {b : BitVec 32} {o n : Nat} {s t : State} (h : AccKeep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩
theorem PowersKeep.of_keep {b : BitVec 32} {o n : Nat} {s t : State} (h : Keep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩

theorem loadCheckpoint_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa loadCheckpoint s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b (1600 + 128 * j) ∧
      point (env t.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 1600 j (by omega) hj
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun t ⟨pt, lt, kt⟩ => ?_
  refine ⟨(AccKeep.of_keep ka).trans (ka'.trans (AccKeep.of_table kt (by decide) (by decide))), lt, ?_, ?_, ?_⟩
  · rw [pt, hm]
    exact workspace_tablePoint ka.frame (by omega) (by omega)
  · rw [point_congr (e := env t.mem b) (f := env a'.mem b) 17 18 19 20
      (kt.high 17 (by decide)) (kt.high 18 (by decide)) (kt.high 19 (by decide)) (kt.high 20 (by decide)),
      hm, ea, savePoint_eval]
  · rw [kt.high 16 (by decide), hm, ea, savePoint_d]

theorem prepareBatch_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => PowersKeep base 5696 2048 s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem base (5696 + 128 * i) =
        powerPoint (tablePoint s.mem base (1600 + 128 * j)) i) ∧ env t.mem base 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (loadCheckpoint_ok hc hl j hj h11) fun a ⟨ka, la, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (ka.ctx hc) la 5696 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨lb, bt, _, bh, kb⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨((PowersKeep.of_acc ka).trans kb).trans (PowersKeep.of_keep kt), lt, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval,
      point_congr (e := env b.mem base) (f := env a.mem base) 17 18 19 20
        (bh 17 (by decide)) (bh 18 (by decide)) (bh 19 (by decide)) (bh 20 (by decide)), av]
  · intro i hi
    have htab := bt i hi
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul] at htab
    exact (workspace_tablePoint kt.frame (by omega) (by omega)).trans
      (htab.trans (congrArg (fun p => powerPoint p i) ap))
  · rw [et, restorePoint_d, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.Arm
