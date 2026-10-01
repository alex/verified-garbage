import VerifiedGarbage.Proof.Ed25519.Arm.VerifyContract

/-! Untrusted: save registers, install public headers, and establish the verifier context. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifySetup_ok {s : State} (h : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VerifyContext (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) t ∧
      ScalarSaved (State.addr (s.gpr .r3)) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r3), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; exact List.mem_singleton_self _
  unfold verifySetup
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl h.f3 hw) fun u ⟨us, uf, ug, uk⟩ => ?_
  refine WP.mono (verifyHeaders_ok (by rw [ug]) h.f3 (by rw [uk.wr]; exact hw))
    fun t ⟨tc, tk, tf, tp, ts, th⟩ => ?_
  have kt := (uk.mono (by decide)).trans tk
  have ft : Frame [⟨State.addr (s.gpr .r3), 8192⟩] s.mem t.mem :=
    (uf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
    (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  have ip (r : Reg) (n : Nat) (hn : (s.gpr r).toNat + n ≤ 2 ^ 32)
      (hi : (⟨State.addr (s.gpr r), n⟩ : Region) ∈ s.rd)
      (hd : (⟨State.addr (s.gpr r), n⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩) :
      VerifyInput (s.gpr .r3) (s.gpr r) n t := by
    refine ⟨hn, fun i hb => ?_, hd⟩
    rw [kt.rd, kt.wr]
    exact in_base (List.mem_append_left _ hi) (by omega) (by omega)
  refine ⟨⟨tc, ip .r0 32 h.f0 (by rw [h.rd]; simp) h.pk_ws,
    ip .r1 64 h.f1 (by rw [h.rd]; simp) h.sig_ws,
    ip .r2 64 h.f2 (by rw [h.rd]; simp) h.challenge_ws,
    tp.trans (congrFun ug .r0), ts.trans (congrFun ug .r1), th.trans (congrFun ug .r2)⟩,
    ?_, kt, ft⟩
  exact us.frame tf fun r hr i hi => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
