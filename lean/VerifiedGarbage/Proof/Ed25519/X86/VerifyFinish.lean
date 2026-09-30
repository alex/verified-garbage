import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyFinish_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4)
    (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.block verifyFinish) s fun t => abiPreserved s₀ t ∧ t.gpr .eax = s.gpr .eax ∧ t.mem = s.mem := by
  simp only [verifyFinish, List.append_assoc]
  refine WP.block_append (Wp.wp_mov fun a ka => WP.block_nil ?_)
  have ca := (updKeep ka).ctx (hs.ctx hp.fit hp.wr)
  refine WP.block_append (WP.mono (abiRestore_regs_ok ca) fun b ⟨mb, sb, bb, ib, pb, db, eb, _, _⟩ => ?_)
  refine Wp.wp_mov fun t kt => WP.block_nil ?_
  have mt : t.mem = s.mem := kt.mem.trans (mb.trans ka.mem)
  have saved : ∀ j < 4, wd a.mem (arg s₀ 3) (4 * j) = s₀.gpr (savedReg j) := by
    intro j hj
    rw [ka.mem]; exact hs.saved j hj
  refine ⟨⟨?_, ?_⟩, ?_, mt⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [kt.other _ (by decide), bb]; exact saved 0 (by decide)
    · rw [kt.other _ (by decide), ib]; exact saved 1 (by decide)
    · rw [kt.other _ (by decide), db]; exact saved 2 (by decide)
    · rw [kt.other _ (by decide), pb]; exact saved 3 (by decide)
    · rw [kt.other _ (by decide), sb, ka.other _ (by decide)]; exact hs.esp
  · rw [mt]
    exact hs.frame.readW (Region.contains_self _ _)
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc) (by decide)
  · rw [kt.gpr, eb, ka.gpr]

end VG.Proof.Ed25519.X86
