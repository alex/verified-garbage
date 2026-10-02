import VerifiedGarbage.Proof.AesGcm.Arm.TextAbsorb

/-!
# AES-GCM on ARMv7: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text otherwise)
and absorbs them, then the lengths block, and writes the tag to `W + o`
(`finTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem disj_sub {X : Region} {rs rs' : List Region} (h : ∀ r ∈ rs', X.Disjoint r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : ∀ r ∈ rs, X.Disjoint r := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr; exact (h r' hr').sub_right hsub

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : BitVec 32} {o : Nat} :
    ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ tagFrame st w sp o, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_tagFrame {st w sp : BitVec 32} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (tagFrame st w sp o) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (c st w sp k8 : BitVec 32) (na : Nat) (s₀ : State) (o R : Nat) (H : Block) (a ct : List Byte)
    (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  args : ArgsKeep na s₀ s
  out : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (arg s₀ 1 ++ arg s₀ 0).toNat ct.length)]
        ^^^ ciphOf m₀ (State.addr c) R (blockAt m₀ (State.addr st)))
  frame : Frame (tagFrame st w sp o) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_ok {na : Nat} (hna : 4 ≤ na) {s₀ s : State} {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block}
    {a ct : List Byte} (he : Env c st w sp k7 k8 s) (hk : ArgsKeep na s₀ s) (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32)
    (hin : args s₀ na ∈ s₀.rd) (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r)
    (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s (FinOut c st w sp k8 na s₀ o R H a ct s.mem) := by
  have hlt := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa tlenZero s = some s₁ ∧
      s₁.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [z_sub0, ← hP]
      exact decide_eq_decide.mpr (or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  -- `r6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s₁ fun s₂ =>
      (s₂.gpr .r6).toNat % 16 = (ghashInput a ct).length % 16 ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
        Keeps s₁ s₂ := by
    refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf₁ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      subst hc
      obtain ⟨i0, v0⟩ := hk₁.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_, ?_, ?_⟩
      · simp [gpr_setReg, v0, Proof.Gcm.ghashInput_nil, ha]
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₁
      obtain ⟨i2', v2'⟩ := hk₁.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2', v2'], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, v2', Proof.Gcm.ghashInput_of_ne hc, List.length_append,
          Proof.Gcm.length_zeros, lowTo_mod16 hP]
        have := Proof.Gcm.length_pad_mod a.length; omega
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h6₂, hg₂, hK₂⟩ => ?_)
  obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((ghashInput a ct).length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, and15, h6₂]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hK₀₃ : Keeps s s₃ := (hK₁.trans hK₂).trans hK₃
  have he₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hg₃ _ (by decide), hg₂ _ (by decide), hg₁ _ (by decide) (by decide)]) hK₀₃.sp hK₀₃.rd hK₀₃.wr
  have hk₃ := hk.of_eq hK₀₃.mem hK₀₃.sp hK₀₃.rd hK₀₃.wr
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₃, by rw [hK₀₃.mem]; exact hH⟩ h6₃)) fun s₄ hh => ?_)
  obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
  have hk₄ := hk₃.frame hf hfl.frame (disj_sub hA tFrame_sub) sp₄ rd₄ wr₄
  have hf₄ := hfl.frame
  rw [hK₀₃.mem] at hf₄
  -- the lengths
  obtain ⟨j0, w0⟩ := hk₄.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨j1, w1⟩ := hk₄.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨j2, w2⟩ := hk₄.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨j3, w3⟩ := hk₄.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8,
      .ldrSp .r7 12] s₄ = some s₅ ∧ s₅.gpr .r4 = arg s₀ 0 ∧ s₅.gpr .r5 = arg s₀ 1 ∧ s₅.gpr .r6 = arg s₀ 2 ∧
      s₅.gpr .r7 = arg s₀ 3 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, w0]
    · simp [gpr_setReg, w1]
    · simp [gpr_setReg, w2]
    · simp [gpr_setReg, w3]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := hfl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅ h8 hR (H := H) (by rw [hK₅.mem]; exact hfl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, hP, hK₅.mem] at tg
  refine ⟨⟨_, tg.env⟩, hk₄.frame hf tg.frame hA (sp₆.trans hK₅.sp) (rd₆.trans hK₅.rd) (wr₆.trans hK₅.wr), fun hab => ?_, ?_⟩
  · rw [tg.out]
    have hw := (hfl.abs (by rw [hK₀₃.mem]; exact hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
    rw [hw, ciph_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.cs.sub_right (Lay.stSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.kc.symm) hR,
      blockAt_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
            (by decide)
        · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm)]
  · exact (t_tagFrame hf₄).trans tg.frame

end

end VG.Proof.AesGcm.Arm
