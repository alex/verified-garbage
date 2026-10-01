import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem q_congr (e f : Env) (h : ∀ i : Slot, 4 ≤ i.val → e i = f i) :
    point e 4 5 6 7 = point f 4 5 6 7 :=
  point_congr 4 5 6 7 (h 4 (by decide)) (h 5 (by decide)) (h 6 (by decide)) (h 7 (by decide))

theorem field_table_same {x : BitVec 32} {s t : State} (h : FieldKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : 928 ≤ o) (hn : o + 128 ≤ 8192) : tablePoint t.mem x o = tablePoint s.mem x o :=
  tablePoint_frame hc.fit h.frame (by decide) hn (Or.inr ho)

theorem verifyCombine_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block verifyCombine) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x 7936 ∧
      point (env t.mem x) 4 5 6 7 =
        Spec.Ed25519.pointAdd (tablePoint s.mem x 7808) (point (env s.mem x) 0 1 2 3) := by
  rw [verifyCombine, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok copyPointToQOps hc) fun a ⟨ka, ea⟩ => ?_
  have ad : env a.mem x 16 = Spec.Ed25519.d := by rw [ea]; exact hd
  have aq : point (env a.mem x) 4 5 6 7 = point (env s.mem x) 0 1 2 3 := by rw [ea, copyPointToQ_eval]
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok (ka.ctx hc) 7808 (by decide) (by decide)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  have bd : env b.mem x 16 = Spec.Ed25519.d := (bh 16 (by decide)).trans ad
  rw [WP.block_append_iff]
  refine WP.mono (pointAdd_ok (kab.ctx hc) bd) fun c ⟨kc, cp, _⟩ => ?_
  have bl : point (env b.mem x) 0 1 2 3 = tablePoint s.mem x 7808 :=
    bp.trans (field_table_same ka hc 7808 (by decide) (by decide))
  have bq : point (env b.mem x) 4 5 6 7 = point (env s.mem x) 0 1 2 3 := (q_congr _ _ bh).trans aq
  have cv := cp.trans (congrArg₂ Spec.Ed25519.pointAdd bl bq)
  have kabc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok copyPointToQOps (kabc.ctx hc)) fun d ⟨kd, ed⟩ => ?_
  have dq : point (env d.mem x) 4 5 6 7 =
      Spec.Ed25519.pointAdd (tablePoint s.mem x 7808) (point (env s.mem x) 0 1 2 3) := by
    rw [ed, copyPointToQ_eval]
    exact cv
  have kabcd := kabc.trans kd
  refine WP.mono (pointTableRead_ok (kabcd.ctx hc) 7936 (by decide) (by decide)) fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨kabcd.trans kt, tp.trans (field_table_same kabcd hc 7936 (by decide) (by decide)), (q_congr _ _ th).trans dq⟩

end VG.Proof.Ed25519.X86
