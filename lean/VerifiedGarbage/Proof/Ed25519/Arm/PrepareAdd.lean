import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.Arm.AccKeep
import VerifiedGarbage.Proof.Ed25519.Arm.PointPowers

/-! Untrusted: save the accumulator and load the next exact power into Q. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem prepareAdd_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa prepareAdd s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 4 5 6 7 = tablePoint s.mem b (5696 + 128 * j) ∧
      point (env t.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 5696 j (by omega) (by omega)
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun c ⟨pc, lc, kc⟩ => ?_
  have kc' : AccKeep b a' c := AccKeep.of_table kc (by decide) (by decide)
  have ks : AccKeep b s c := (AccKeep.of_keep ka).trans (ka'.trans kc')
  have savec : point (env c.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [point_congr _ _ _ _ (kc.high 17 (by decide)) (kc.high 18 (by decide))
      (kc.high 19 (by decide)) (kc.high 20 (by decide)), hm, ea, savePoint_eval]
  have dc : env c.mem b 16 = env s.mem b 16 := by rw [kc.high 16 (by decide), hm, ea, savePoint_d]
  have tc : tablePoint a'.mem b (5696 + 128 * j) = tablePoint s.mem b (5696 + 128 * j) := by
    rw [hm]
    exact workspace_tablePoint ka.frame (by omega) (by omega)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (ks.ctx hc) lc) fun d ⟨kd, ld, ed⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kd.ctx (ks.ctx hc)) ld) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨ks.trans ((AccKeep.of_keep kd).trans (AccKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_q, ed, copyPointToQ_eval, pc, tc]
  · rw [et, restorePoint_saved, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_d, ed, copyPointToQ_d, dc]

end VG.Proof.Ed25519.Arm
