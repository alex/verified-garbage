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
  refine WP.block_append (WP.mono (abiRestore_ok (g := s₀.gpr) ca (by rw [ka.mem]; exact hs.saved))
    fun b ⟨gb, sb, eb, mb⟩ => ?_)
  refine Wp.wp_mov fun t kt => WP.block_nil ?_
  have mt : t.mem = s.mem := kt.mem.trans (mb.trans ka.mem)
  refine ⟨⟨?_, ?_⟩, ?_, mt⟩
  · intro r hr
    rw [kt.other r fun e => absurd (e ▸ hr) (by decide)]
    by_cases h : r = .esp
    · subst h; rw [sb, ka.other _ (by decide)]; exact hs.esp
    · exact gb r hr h
  · rw [mt]
    exact hs.frame.readW (Region.contains_self _ _)
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc) (by decide)
  · rw [kt.gpr, eb, ka.gpr]

end VG.Proof.Ed25519.X86
