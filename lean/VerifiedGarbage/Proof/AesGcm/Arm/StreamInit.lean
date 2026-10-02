import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `stream_init` saves our
caller's registers in `scratch` (`W`) and writes the state's `J₀`, its zero
accumulator and its first counter block with `j0` (`streamInit_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

/-- The layout of `stream_init`. -/
theorem siLay {s₀ : State} (h : streamInitArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, -, fs, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SI1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r1
  r5 : s₁.gpr .r5 = s₀.gpr .r2
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : SavedAt s₁.mem (arg s₀ 0) s₀
  frame : Frame [savedR (arg s₀ 0)] s₀.mem s₁.mem

theorem si1_wp {s₀ : State} (h : streamInitArm.pre s₀) : WP isa (.block streamInitPre) s₀ (SI1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r3), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 0), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha := arg_in (s := s₀) (n := 1) (i := 0) (by decide) spf (by rw [hrd]; simp)
  refine entry_ok (off := 0) (by decide) ha fW hW fun s₁ g12 g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12, stackArg_zero]
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact rd
  · exact wr

theorem si_j0In {s₀ s₁ : State} (h : streamInitArm.pre s₀) (h1 : SI1 s₀ s₁) :
    J0In (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (s₀.gpr .r1) (s₀.gpr .r2).toNat s₁ := by
  have L := siLay h
  obtain ⟨hrd, -, -, -, dns, dnW, -, -, -, -, bn, -, -, -, fn, -, -, -, -⟩ := h
  refine ⟨h1.env, ?_, h1.r4, by rw [h1.r5]; simp, ⟨?_, (s₀.gpr .r2).isLt, fn, dns, dnW, bn⟩⟩
  · rw [ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)

/-- After `j0`. -/
def SI2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, SI1 s₀ s₁ ∧ J0Out (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r8)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) s₁.mem s₂

theorem si_fin {s₀ s₂ : State} (h : streamInitArm.pre s₀) (h2 : SI2 s₀ s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' := by
  have L := siLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  obtain ⟨k7, he⟩ := ho.env
  obtain ⟨-, -, -, -, -, dnW, -, -, -, -, -, -, -, -, fn, -, fW, -, -⟩ := h
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (saved_j0Frame L)) he.sp)
    fun s' hh => ⟨hh.1, fun ciph => ?_⟩
  have hm := hh.2.1
  have hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega)
  have hj := ho.j0; have hy := ho.y; have hcb := ho.cb
  rw [hiv] at hj hcb
  rw [Proof.Gcm.streamRepr_iff, hm, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit]
  exact ⟨hj, Proof.Gcm.absorbed_nil _ hy, Proof.Gcm.ctr_zero _ _ _ _ hcb⟩

theorem streamInit_wp {s₀ : State} (h : streamInitArm.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' :=
  WP.seq (WP.mono (si1_wp h) fun s₁ h1 => WP.seq (WP.mono (j0_ok (siLay h) (si_j0In h h1)) fun _ ho =>
    si_fin h ⟨s₁, h1, ho⟩))

end VG.Proof.AesGcm.Arm
