import VerifiedGarbage.Proof.Ed25519.X86.CommonContract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLoop

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarInit) s fun t => ScalarKeep s t ∧ t.gpr .esi = 64 ∧
      Frame [sub x scalarR 32] s.mem t.mem ∧ fe t.mem x scalarR = 0 := by
  simp only [scalarInit, List.append_assoc]
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.block_append (WP.mono (cols_ok (ku.ctx hc) (fun _ => []) 8 (by decide)
    (fun _ _ _ h => by simp only [List.not_mem_nil] at h)
    (fun _ _ => by change 0 < 2 ^ 68; decide) (by rw [au]; decide)) fun v ⟨kv, fv, ev, _⟩ => ?_)
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  have hz : fe v.mem x scalarR = 0 := by
    change fe v.mem x scalarR + _ * _ = acc u + 0 at ev
    rw [au] at ev
    omega_using [ev]
  refine ⟨(Keep.scalar ku).trans ((Keep.scalar kv).trans (scalarUpd ht)), ht.gpr, ?_, ?_⟩
  · rw [ht.mem, mu] at *; exact fv
  · rw [ht.mem]; exact hz

theorem scalarEngine_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa scalarEngine s fun t => ScalarKeep s t ∧ Frame (scalarBodyFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = Spec.Ed25519.decodeLE (scalarInput s.mem x) % Spec.Ed25519.L := by
  refine WP.seq (WP.mono (scalarInit_ok hc) fun u ⟨ku, su, fu, vu⟩ => ?_)
  refine WP.mono (scalarLoop_ok (ku.ctx hc) su vu) fun t ⟨kt, ft, vt⟩ => ?_
  have fm : Frame (scalarBodyFrame x) s.mem u.mem := fu.mono fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have input : scalarInput u.mem x = scalarInput s.mem x := List.map_congr_left fun i hi =>
    scalarInput_byte hc.fit fm (List.mem_range.mp hi)
  exact ⟨ku.trans kt, fm.trans ft, by rw [vt, input]⟩

theorem Saved.scalarEngine {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : ScalarKeep s t)
    (hf : Frame (scalarBodyFrame x) s.mem t.mem) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [scalarBodyFrame, scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [scR_eq] <;>
      exact sub_sub hx (by decide) (by decide) (by decide)
  · have hR : scalarR = 64 := rfl
    have hT : T = 864 := rfl
    intro p hp r hr
    have hj := savedSlots_bound p hp
    simp only [scalarBodyFrame, scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact sub_disj (by omega_using [hx, hj]) (by omega_using [hx, hR, hT])
        (Or.inl (by omega_using [hj, hR, hT]))
end VG.Proof.Ed25519.X86
