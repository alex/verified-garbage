import VerifiedGarbage.Proof.AesGcm.Arm.StreamInit
import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. `stream_aad` saves our
caller's registers in `scratch` (`W`) and absorbs the additional data into
GHASH with `absorb` (`streamAad_wp`), with `len(A) mod 16` from the low
word of `aad_len`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

theorem saLay {s₀ : State} (h : streamAadArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, fs, -, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SA1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = arg s₀ 0
  r5 : s₁.gpr .r5 = arg s₀ 1
  r6 : s₁.gpr .r6 = BitVec.ofNat 32 ((s₀.gpr .r2).toNat % 16)
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : SavedAt s₁.mem (arg s₀ 2) s₀
  frame : Frame [savedR (arg s₀ 2)] s₀.mem s₁.mem

theorem sa1_wp {s₀ : State} (h : streamAadArm.pre s₀) : WP isa (.block streamAadPre) s₀ (SA1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r1), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 2), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 3, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => arg_in (n := 3) hi spf (by rw [hrd]; simp)
  have hA : ∀ r ∈ [savedR (arg s₀ 2)], (args s₀ 3).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  refine entry_ok (off := 8) (by decide) (ha 2 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have a₀ := ha 0 (by decide); have a₁ := ha 1 (by decide)
  rw [← rd, ← wr, ← sp] at a₀ a₁
  have e₀ := arg_frame (s' := s₁) sp spf fr hA (i := 0) (by decide)
  have e₁ := arg_frame (s' := s₁) sp spf fr hA (i := 1) (by decide)
  rw [stackArg_zero] at e₀
  simp only [stackArg_eq, Nat.mul_one] at e₁ a₁
  simp only [Nat.mul_zero] at a₀
  have hand := and15 (s₀.gpr .r2)
  refine WP.of_runBlock ⟨_, by arun [a₀, a₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12, hand]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · simp [gpr_setReg, e₀]
  · simp [gpr_setReg, e₁, stackArg]; rfl
  · exact rd
  · exact wr

theorem sa_absIn {s₀ s₁ : State} (h : streamAadArm.pre s₀) (h1 : SA1 s₀ s₁) {x : List Byte}
    (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    AbsIn (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (arg s₀ 0) (arg s₀ 1).toNat s₁ := by
  have L := saLay h
  obtain ⟨hrd, -, -, -, dDs, dDW, -, -, -, -, bD, -, -, -, -, fD, -, -, -⟩ := h
  refine ⟨h1.env, h1.r4, by rw [h1.r5]; simp, by rw [h1.r6, hx], ⟨?_, (arg s₀ 1).isLt, fD, dDs, dDW, bD⟩, ?_⟩
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)
  · rw [ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]

/-- After `absorb`. -/
def SA2 (s₀ : State) (x : List Byte) (s₂ : State) : Prop :=
  ∃ s₁, SA1 s₀ s₁ ∧ AbsOut (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (x ++ bytesAt s₁.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) s₁.mem s₂

theorem sa_fin {s₀ s₂ : State} (h : streamAadArm.pre s₀) {x : List Byte} (h2 : SA2 s₀ x s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) [] := by
  have L := saLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  have he := ho.env
  obtain ⟨-, -, -, -, -, dDW, dsW, -, -, -, -, -, -, -, -, fD, fW, -, -⟩ := h
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (saved_absFrame L (.inr rfl)))
    he.sp) fun s' hh => ⟨hh.1, fun ciph iv hs => ?_⟩
  have hm := hh.2.1
  have hd : bytesAt s₁.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))) (by omega)
  have hab := ho.abs
  rw [hd] at hab
  have dS : ∀ {d : Nat}, d + 16 ≤ 80 → ∀ r ∈ [savedR (arg s₀ 2)],
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w hd (.inr ⟨by decide, by decide⟩)
  have dA : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) → ∀ r ∈ absFrame (s₀.gpr .r1) (arg s₀ 2) s₀.sp 16,
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have keep : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) →
      blockAt s'.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) =
        blockAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) := fun hd => by
    rw [hm, blockAt_frame ho.frame (dA hd), blockAt_frame h1.frame (dS (by omega))]
  rw [Proof.Gcm.streamRepr_iff] at hs ⊢
  obtain ⟨hj, ha, hc⟩ := hs
  simp only [ofNat_lit] at hj ha hc ⊢
  refine ⟨by simpa using (keep (d := 0) (.inl rfl)).trans (by simpa using hj), ?_, ?_⟩
  · rw [hm]
    refine hab (ha.congr ?_ ?_)
    · rw [blockAt_frame h1.frame (dS (by decide))]
    · rw [bytesAt_frame h1.frame (fun r hr => (dS (d := 32) (by decide) r hr).sub_left
        (Region.sub_prefix (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega)))
        (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega)]
  · exact hc.congr (keep (.inr (.inl rfl))) (keep (.inr (.inr rfl)))

theorem sa_run {s₀ : State} (h : streamAadArm.pre s₀) {x : List Byte} (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) [] :=
  WP.seq (WP.mono (sa1_wp h) fun s₁ h1 => WP.seq (WP.mono (absorb_ok (saLay h) (.inr rfl) (sa_absIn h h1 hx))
    fun _ ho => sa_fin h ⟨s₁, h1, ho⟩))

theorem streamAad_wp {s₀ : State} (h : streamAadArm.pre s₀) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ streamAadArm.post s₀ s' := by
  have h₀ := sa_run h (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : (Block → Block) × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) i.1 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.2.1 i.2.2 [] ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.2.length)
    fun i hi => WP.mono (sa_run h (x := i.2.2) (low_mod16 hi.2).symm) fun _ hh => hh.2 i.1 i.2.1 hi.1)
    fun s' hh => ⟨hh.1, fun ciph iv a hs hl => hh.2 ⟨ciph, iv, a⟩ ⟨hs, hl⟩⟩

end VG.Proof.AesGcm.Arm
