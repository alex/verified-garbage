import VerifiedGarbage.Proof.Ed25519.X86_64.RootPower

/-! Untrusted: lift the root exponentiation into Ed25519's larger scratch region. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr IKeep)

theorem rootPowerWide_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa Impl.Ed25519.X86_64.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv⟩ := rootPower_spec base narrow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, ?_⟩
  · have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
    simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e
  · change VG.Proof.X25519.X86_64.E t.mem base 17 = _
    rw [hv, rootEnv_eval, rootPower_eq]
    rfl

end VG.Proof.Ed25519.X86_64
