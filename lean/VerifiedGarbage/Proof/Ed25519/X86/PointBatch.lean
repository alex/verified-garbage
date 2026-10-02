import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
import VerifiedGarbage.Proof.Ed25519.X86.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd

/-! Each batch contains sixteen consecutive exact powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem loadCheckpoint_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block loadCheckpoint) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x (1024 + 128 * j) ∧
      point (env t.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 ∧
      env t.mem x 16 = env s.mem x 16 := by
  simp only [loadCheckpoint, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok savePointOps hc) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 1024 j (by omega) (ka.keep.esi.trans hb))
    fun b ⟨kb, mb, pb⟩ => ?_
  have cb := kb.ctx (ka.ctx hc)
  refine WP.mono (pointFromTable_ok cb pb (by omega) (by omega)) fun c ⟨kc, pc⟩ => ?_
  refine ⟨ka.trans ((FieldKeep.of_mem kb mb).trans (FieldKeep.of_copy kc cb)), ?_, ?_, ?_⟩
  · rw [pc, mb]
    exact workspace_table (IKeep.of_field ka) hc _ (by omega) (by omega)
  · rw [point_congr _ _ _ _ (kc.high cb 17 (by decide)) (kc.high cb 18 (by decide))
      (kc.high cb 19 (by decide)) (kc.high cb 20 (by decide)), mb, ea, savePoint_eval]
  · rw [kc.high cb 16 (by decide), mb, ea, savePoint_d]

theorem prepareBatch_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => PowersKeep x 5120 2048 s t ∧
      point (env t.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem x (5120 + 128 * i) =
        powerPoint (tablePoint s.mem x (1024 + 128 * j)) i) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (loadCheckpoint_ok hc j hj hb) fun a ⟨ka, pa, sa, da⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (ka.ctx hc) 5120 16 (by decide) (by decide)
    (by decide) (by decide) (da.trans hd)) fun b ⟨kb, tb, _, high⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc))) fun t ⟨kt, et⟩ => ?_
  refine ⟨((PowersKeep.of_ikeep (IKeep.of_field ka) _ _).trans kb).trans
    (PowersKeep.of_ikeep (IKeep.of_field kt) _ _), ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval, point_congr _ _ _ _ (high 17 (by decide)) (high 18 (by decide))
      (high 19 (by decide)) (high 20 (by decide)), sa]
  · intro i hi
    rw [workspace_table (IKeep.of_field kt) (kb.ctx (ka.ctx hc)) _ (by omega) (by omega), tb i hi, pa]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [et, restorePoint_d, high 16 (by decide), da, hd]

end VG.Proof.Ed25519.X86
