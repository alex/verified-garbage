import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch

/-!
# AES-GCM on whole blocks, x86-64: correctness

Untrusted: everything here is checked by Lean. The entry, the first
`16 ⌊n / 16⌋` blocks in one pass (with `stitch`), and the rest
(`encrypt_wp`, `decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {s : State} (hp : BP s)
include hp

/-- With nothing left, `Mid` is the end, when encrypting. -/
theorem encDone_of {q : Nat} {st : State} (M : Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st)
    (h0 : n s - q = 0) : EncDone s st := by
  have hq : q = n s := by have := M.q_le; omega
  subst hq
  exact ⟨⟨M.saved, keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

/-- With nothing left, `Mid` is the end, when decrypting. -/
theorem decDone_of {q : Nat} {st : State} (M : Mid s q q (blocksAt s.mem (D s) q) st) (h0 : n s - q = 0) :
    DecDone s st := by
  have hq : q = n s := by have := M.q_le; omega
  subst hq
  exact ⟨⟨M.saved, keep_r hp M.frame⟩, M.data, M.ctr, M.y⟩

end

theorem encrypt_wp (v : GcmImpl) (stitch : Bool) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (encrypt v.callees.ctr v.callees.gh stitch) s (EncDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st →
      WP isa (tail (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st (EncDone s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => encDone_of hp M' h0) fun _ M' hlt => encCalls_ok hp v M' hlt
  cases stitch
  · exact WP.seq (WP.block_nil (tl 0 s₁ (mid_entry hp hg hk hf hrd hwr)))
  · exact WP.seq (WP.mono (stitchE_ok hp h11 hg hk hf hrd hwr) fun st M => tl _ st M)

theorem decrypt_wp (v : GcmImpl) (stitch : Bool) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (decrypt v.callees.ctr v.callees.gh stitch) s (DecDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, Mid s q q (blocksAt s.mem (D s) q) st →
      WP isa (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st (DecDone s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => decDone_of hp M' h0) fun _ M' hlt => decCalls_ok hp v M' hlt
  cases stitch
  · exact WP.seq (WP.block_nil (tl 0 s₁ (mid_entry hp hg hk hf hrd hwr)))
  · exact WP.seq (WP.mono (stitchD_ok hp h11 hg hk hf hrd hwr) fun st M => tl _ st M)

end VG.Proof.AesGcm.X86_64.Blocks
