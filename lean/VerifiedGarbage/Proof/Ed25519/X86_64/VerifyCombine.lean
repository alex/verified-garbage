import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyTables

/-! Untrusted: add R to [k]A and load [S]B for the projective comparison. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

private theorem q_congr (e f : Env) (h : ∀ i : Slot, 4 ≤ i.val → e i = f i) :
    point e 4 5 6 7 = point f 4 5 6 7 := by
  simp only [point, h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem verifyCombine_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block verifyCombine) s fun t => RbxKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base 7680 ∧
      point (env t.mem base) 4 5 6 7 =
        Spec.Ed25519.pointAdd (tablePoint s.mem base 7552) (point (env s.mem base) 0 1 2 3) := by
  rw [verifyCombine, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs copyPointToQOps) fun a ⟨ka, va⟩ => ?_
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact hd
  have aq : point (env a.mem base) 4 5 6 7 = point (env s.mem base) 0 1 2 3 := by
    rw [va, copyPointToQ_eval]
  rw [WP.block_append_iff]
  refine WP.mono (pointTableRead_ok (hs.of_keep ka) 7552 (by decide) (by decide)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := (RbxKeep.of_keep ka).trans kb
  have bd : env b.mem base 16 = Spec.Ed25519.d := (bh 16 (by decide)).trans ad
  rw [WP.block_append_iff]
  refine WP.mono (pointAddWide_ok (kab.scratch hs) bd) fun c ⟨kc, cp, _⟩ => ?_
  have cv : point (env c.mem base) 0 1 2 3 =
      Spec.Ed25519.pointAdd (tablePoint s.mem base 7552) (point (env s.mem base) 0 1 2 3) := by
    rw [cp, bp, workspace_tablePoint ka.mem (by decide) (by decide), q_congr _ _ bh, aq]
  have kabc := kab.trans (RbxKeep.of_keep kc)
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (kabc.scratch hs) copyPointToQOps) fun d ⟨kd, vd⟩ => ?_
  have dq : point (env d.mem base) 4 5 6 7 =
      Spec.Ed25519.pointAdd (tablePoint s.mem base 7552) (point (env s.mem base) 0 1 2 3) := by
    rw [vd, copyPointToQ_eval, cv]
  have kabcd := kabc.trans (RbxKeep.of_keep kd)
  refine WP.mono (pointTableRead_ok (kabcd.scratch hs) 7680 (by decide) (by decide)) fun t ⟨kt, tp, th⟩ => ?_
  refine ⟨kabcd.trans kt, ?_, ?_⟩
  · rw [tp, workspace_tablePoint kabcd.mem (by decide) (by decide)]
  · rw [q_congr _ _ th, dq]

end VG.Proof.Ed25519.X86_64
