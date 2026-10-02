import VerifiedGarbage.Proof.AesGcm.X86_64.Contract

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `J₀`, the accumulator and the
first counter block, from `j0` (`streamInit_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

/-- `vg_aes_gcm_stream_init`. -/
theorem streamInit_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamInitX86_64.pre s) :
    WP isa (streamInit v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamInitX86_64.post s s' := by
  simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp ⊢
  obtain ⟨hrd, hwr, d_cs, d_cw, d_ns, d_nw, d_sw, r_s, r_w, k_c, k_n, k_s, k_w, wc, wn, ws, ww⟩ := hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hSt : s.gpr .rcx = St at *
  generalize hW : s.gpr .r8 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hn : (s.gpr .rdx).toNat = n at *
  have L : Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .r8 hW pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi),
        .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = Np ∧
      s₂.gpr .rbp = BitVec.ofNat 64 n ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hNp]
    · simp [gpr_setReg, hg₁, ← hn]
    · simp [gpr_setReg, hg₁, hSP]
    all_goals rfl
  have he₂ : Env Ctx St W SP s₂ := ⟨h13, h14, h15, hg₂, by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW⟩
  have rdN : Covers [⟨Np, n⟩] (s₂.rd ++ s₂.wr) := by
    rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hiv : bytesAt s₂.mem Np n = bytesAt s.mem Np n := by
    rw [hm₂]; exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_nw.sub_right (Lay.wSub (by decide))) (by omega)
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [hm₂, ctxH_eq, blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)]
  have hji : J0In Ctx St W SP (ctxH s.mem Ctx) Np n s₂ :=
    ⟨he₂, hH, h12, hbp, ⟨rdN, by have := (s.gpr .rdx).isLt; omega, wn, d_ns, d_nw, k_n⟩⟩
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩))
  refine WP.seq (WP.mono (j0_ok v L hji) fun s₃ ho => ?_)
  have he₃ := ho.env
  have hret : s₃.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept ho.frame (fun r hr => ?_), hm₂, ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact r_s
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok he₃.r15 (by rw [he₃.rsp, hSP]) (covers_left he₃.perm.w)
    ((hm₂ ▸ hsv₁).frame ho.frame (saved_j0Frame L)) (by rw [hSP, hret])) fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ciph => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, ← hiv]
  refine ⟨ho.j0, Proof.Gcm.absorbed_nil _ ho.y, ho.cb, fun h => absurd rfl h⟩

end VG.Proof.AesGcm.X86_64
