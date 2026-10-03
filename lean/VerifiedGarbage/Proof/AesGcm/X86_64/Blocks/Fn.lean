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
    (h0 : n s - q = 0) : InFrame Proof.AesGcm.encryptBlocksX86_64.post s st := by
  have hq : q = n s := by have := M.q_le; omega
  subst hq
  exact ⟨M.rsp, M.wr, M.saved, keep_r hp M.frame, M.data, M.ctr, M.y⟩

/-- With nothing left, `Mid` is the end, when decrypting. -/
theorem decDone_of {q : Nat} {st : State} (M : Mid s q q (blocksAt s.mem (D s) q) st) (h0 : n s - q = 0) :
    InFrame Proof.AesGcm.decryptBlocksX86_64.post s st := by
  have hq : q = n s := by have := M.q_le; omega
  subst hq
  exact ⟨M.rsp, M.wr, M.saved, keep_r hp M.frame, M.data, M.ctr, M.y⟩

/-- The frame: its body from the state after its push, which returns `post`
after its pop. -/
theorem frame_ok {post : State → State → Prop} {body : Prog isa} {s₁ : State} (h11 : s₁.gpr .r11 = S s)
    (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr)
    (hpost : ∀ st st' : State, st'.mem = st.mem → post s st → post s st')
    (hb : ∀ p : State, p.gpr .rsp = F s → p.gpr .r11 = S s → (∀ r, r ≠ .r11 → r ≠ .rsp → p.gpr r = s.gpr r) →
      Kept s 0 p.mem → Frame [fR s] s.mem p.mem → p.rd = s.rd → p.wr = fR s :: s.wr →
      WP isa body p (InFrame post s)) :
    WP isa (.frame (.push frameRegs) body (.pop .rax 7)) s₁ fun s' => gprPreserved s s' ∧ post s s' ∧ True := by
  have hsp : s₁.gpr .rsp = SP s := hg _ (by decide)
  have h56 : 8 * frameRegs.length ≤ (s₁.gpr .rsp).toNat := by rw [hsp]; have := hp.w_sp₀; simp [frameRegs]; omega
  obtain ⟨psp, pk, pf⟩ := pushed_kept hp h11 hg hm
  have pw : (pushed frameRegs s₁).wr = fR s :: s.wr := by
    rw [pushed_wr, hsp, hwr]; rfl
  refine WP.frame (by simp [frameRegs]) (by decide) (by decide) h56 (WP.mono (hb _ psp
    (by rw [pushed_gpr _ _ (by decide)]; exact h11) (fun r h₁ h₂ => by rw [pushed_gpr _ _ h₂]; exact hg r h₁) pk pf
    (by rw [pushed_rd, hrd]) pw) fun s₂ ⟨r₂, w₂, sv₂, ret₂, po₂⟩ => ⟨by rw [r₂, psp], by rw [w₂, pw], ?_, ?_, trivial⟩)
  · refine ⟨fun r hr => ?_, by rw [popped_mem]; exact ret₂⟩
    by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₂, show 8 * frameRegs.length = 56 from rfl]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr)]; exact sv₂ r hr hr'
  · exact hpost _ _ (popped_mem _ _ _) po₂

end

theorem encrypt_wp (v : GcmImpl) (stitch : Bool) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (encrypt v.callees.ctr v.callees.gh stitch) s (EncDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨h11, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.mono (frame_ok hp h11 hg hm hrd hwr (fun _ _ h q => by
    simp only [Proof.AesGcm.encryptBlocksX86_64, h] at q ⊢; exact q) fun p psp p11 pg pk pf prd pwr => ?_) fun _ h => ⟨h.1, h.2.1⟩
  have tl : ∀ q st, Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st →
      WP isa (tail (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st
        (InFrame Proof.AesGcm.encryptBlocksX86_64.post s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => encDone_of hp M' h0) fun _ M' hlt => encCalls_ok hp v M' hlt
  cases stitch
  · exact WP.seq (WP.block_nil (tl 0 p (mid_entry hp psp pg pk pf prd pwr)))
  · exact WP.seq (WP.seq (WP.mono (stitchE_ok hp psp p11 pg pk pf prd pwr) fun st M =>
      WP.mono (rest_ok hp rfl M) fun st' M' => tl _ st' M'))

theorem decrypt_wp (v : GcmImpl) (stitch : Bool) {s : State} (hpre : Proof.AesGcm.blocksPre s) :
    WP isa (decrypt v.callees.ctr v.callees.gh stitch) s (DecDone s) := by
  have hp := BP.of hpre
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨h11, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.mono (frame_ok hp h11 hg hm hrd hwr (fun _ _ h q => by
    simp only [Proof.AesGcm.decryptBlocksX86_64, h] at q ⊢; exact q) fun p psp p11 pg pk pf prd pwr => ?_) fun _ h => ⟨h.1, h.2.1⟩
  have tl : ∀ q st, Mid s q q (blocksAt s.mem (D s) q) st →
      WP isa (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st
        (InFrame Proof.AesGcm.decryptBlocksX86_64.post s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => decDone_of hp M' h0) fun _ M' hlt => decCalls_ok hp v M' hlt
  cases stitch
  · exact WP.seq (WP.block_nil (tl 0 p (mid_entry hp psp pg pk pf prd pwr)))
  · exact WP.seq (WP.seq (WP.mono (stitchD_ok hp psp p11 pg pk pf prd pwr) fun st M =>
      WP.mono (rest_ok hp rfl M) fun st' M' => tl _ st' M'))

end VG.Proof.AesGcm.X86_64.Blocks
