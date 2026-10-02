import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PointPowers

/-! Load a table point while preserving the accumulator for selection. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    FieldKeep x s t := ⟨h, by rw [hm]; exact Frame.refl _ _⟩

theorem FieldKeep.of_copy {x : BitVec 32} {s t : State} (h : CopyKeep x 64 128 s t)
    (hc : Ctx x s) : FieldKeep x s t :=
  ⟨⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr⟩,
    frameWiden h.frame hc.fit (by decide) (by decide) (by decide)⟩

theorem point_congr {e f : Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : point e x y z t = point f x y z t :=
  point_mk_congr hx hy hz ht

theorem savePoint_d (e : Env) : evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : Env) : evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : Env) : evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : Env) :
    point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : Env) :
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem prepareAdd_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (j : Nat) (hj : j < 16) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block prepareAdd) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 ∧
      point (env t.mem x) 4 5 6 7 = tablePoint s.mem x (5120 + 128 * j) ∧
      point (env t.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 ∧
      env t.mem x 16 = env s.mem x 16 := by
  simp only [prepareAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok savePointOps hc) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 5120 j (by omega) (ka.keep.esi.trans hb))
    fun b ⟨kb, mb, pb⟩ => ?_
  have cb := kb.ctx (ka.ctx hc)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok cb pb (by omega) (by omega)) fun c ⟨kc, pc⟩ => ?_
  have ks : FieldKeep x s c := ka.trans ((FieldKeep.of_mem kb mb).trans (FieldKeep.of_copy kc cb))
  have savec : point (env c.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 := by
    rw [point_congr _ _ _ _ (kc.high cb 17 (by decide)) (kc.high cb 18 (by decide))
      (kc.high cb 19 (by decide)) (kc.high cb 20 (by decide)), mb, ea, savePoint_eval]
  have dc : env c.mem x 16 = env s.mem x 16 := by rw [kc.high cb 16 (by decide), mb, ea, savePoint_d]
  have tc : tablePoint b.mem x (5120 + 128 * j) = tablePoint s.mem x (5120 + 128 * j) := by
    rw [mb]
    exact workspace_table (IKeep.of_field ka) hc _ (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok copyPointToQOps (ks.ctx hc)) fun d ⟨kd, ed⟩ => ?_
  refine WP.mono (fieldCode_ok restorePointOps (kd.ctx (ks.ctx hc))) fun t ⟨kt, et⟩ => ?_
  refine ⟨ks.trans (kd.trans kt), ?_, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_q, ed, copyPointToQ_eval, pc, tc]
  · rw [et, restorePoint_saved, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_d, ed, copyPointToQ_d, dc]

end VG.Proof.Ed25519.X86
