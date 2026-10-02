import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
compute the tag from the same lengths and number of rounds (`finTag_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

theorem fin_lay {s : State} (hp : Proof.AesGcm.finPre s) :
    Lay (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r9) (s.gpr .rsp) ∧ Perm (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r9) s ∧
      (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) := by
  simp only [Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, -, -, k_c, k_s, k_w, wc, ws, ww, hR⟩ := hp
  exact ⟨Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w,
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩, ww, hR⟩

theorem finEntry_fin {s : State} (hp : Proof.AesGcm.finPre s) :
    WP isa (.block finEntry) s (FinS (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r9) (s.gpr .rsp) (s.gpr .rsi).toNat
      (s.gpr .rcx) (s.gpr .r8)) := by
  obtain ⟨_, hperm, ww, hR⟩ := fin_lay hp
  exact WP.mono (finEntry_ok rfl rfl rfl rfl hperm ww hR) fun _ e => ⟨e.env, e.rounds, e.alen, e.tlen⟩

theorem streamFinish_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamFinishX86_64.pre s₀') (hq : Proof.AesGcm.streamFinishX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamFinish v.callees) fun _ _ => True := by
  obtain ⟨L, -, -, -⟩ := fin_lay hp
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have hE₂ := finEntry_fin hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇] at hE₂
  refine fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := s₀.gpr .r9) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨_, by taint_decide⟩ (finEntry_fin hp) hE₂ ?_
  have hw : ∀ s, FinS (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r9) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rcx)
      (s₀.gpr .r8) s → WP isa (finTag v.callees 0) s (Env (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .r9) (s₀.gpr .rsp)) :=
    fun s h => WP.mono (finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2.1 h.2.2.2
      (x := List.replicate ((if s₀.gpr .r8 = 0 then (s₀.gpr .rcx).toNat else (s₀.gpr .r8).toNat) % 16) 0)
      (by simp)) fun _ h => h.1
  exact (rel_wp (finTag_rel v L (.inl rfl)) (fun _ _ h => h) hw hw).mono (fun _ _ h => h.2) fun _ _ h => h.2

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamFinishX86_64.pre Proof.AesGcm.streamFinishX86_64.pub
      (streamFinish v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamFinish_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
