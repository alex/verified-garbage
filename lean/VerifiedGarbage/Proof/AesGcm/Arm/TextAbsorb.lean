import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-!
# AES-GCM on ARMv7: absorbing the text (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the `len`
bytes at `data` into GHASH as text: before the first text (`text_len` 0) it
pads the additional data first (`firstFlush`), and it does nothing for no
bytes (`textAbsorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 16, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem lowTo_mod16 {hi lo : BitVec 32} {P : Nat} (h : (hi ++ lo).toNat = P) : lo.toNat % 16 = P % 16 := by
  rw [Proof.Gcm.toNat_append] at h; omega

theorem z_sub0 (x : BitVec 32) : (x - 0#32 == 0) = decide (x.toNat = 0) := by
  by_cases h : x.toNat = 0 <;> simp [BitVec.toNat_eq, h]

theorem or_zero_iff (lo hi : BitVec 32) : (lo ||| hi).toNat = 0 ↔ (hi ++ lo).toNat = 0 := by
  constructor
  · intro h
    have : lo ||| hi = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h)
    rw [BitVec.or_eq_zero_iff] at this
    obtain ⟨rfl, rfl⟩ := this; rfl
  · intro h
    rw [Proof.Gcm.toNat_append] at h
    have h1 : lo = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega)
    have h2 : hi = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst h1 h2; rfl

/-- After `textAbsorb`, from `m₀`: GHASH has absorbed `x`. -/
structure TaOut (c st w sp k7 k8 : BitVec 32) (s₀ : State) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  args : ArgsKeep 7 s₀ s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (taFrame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_taFrame {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') : Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

omit L in
theorem t_taFrame {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') : Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem textAbsorb_ok {s₀ s : State} {H : Block} {a ct : List Byte} (he : Env c st w sp k7 k8 s)
    (hk : ArgsKeep 7 s₀ s) (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : args s₀ 7 ∈ s₀.rd)
    (hA : ∀ r ∈ taFrame st w sp, (args s₀ 7).Disjoint r)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (hd : DataOk st w sp s (arg s₀ 4) (arg s₀ 5).toNat)
    (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa textAbsorb s (TaOut c st w sp k7 k8 s₀ H (ghashInput a ct)
      (ghashInput a (ct ++ bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat)) s.mem) := by
  have hn := (arg s₀ 5).isLt
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₁, run₁, h5₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r5 20, .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r5 = arg s₀ 5 ∧ s₁.z = decide ((arg s₀ 5).toNat = 0) ∧ (∀ r, r ≠ .r5 → s₁.gpr r = s.gpr r) ∧
      Keeps s s₁ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · simp only [z_subFlags, gpr_setReg, ite_true, v5]
      exact z_sub0 _
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hK₁.sp hK₁.rd hK₁.wr
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : (arg s₀ 5).toNat = 0 := by simpa using ht
    rw [h0]
    refine WP.block_nil ⟨he₁, hk₁, by rw [hK₁.mem]; exact hH, fun hab => ?_, by rw [hK₁.mem]; exact Frame.refl _ _⟩
    simp only [bytesAt, List.range_zero, List.map_nil, List.append_nil, hK₁.mem]; exact hab
  have h0 : (arg s₀ 5).toNat ≠ 0 := by simpa using hf'
  -- `Z` iff no text so far
  obtain ⟨i2, v2⟩ := hk₁.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk₁.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₂, run₂, hz₂, hg₂, hK₂⟩ : ∃ s₂, runBlock isa tlenZero s₁ = some s₂ ∧
      s₂.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [z_sub0, ← hP]
      exact decide_eq_decide.mpr (or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := hk₁.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have hm₂ : s₂.mem = s.mem := hK₂.mem.trans hK₁.mem
  -- the additional data padded, before the first text
  let x' := if ct = [] then a ++ zeros (padLen a.length) else ghashInput a ct
  have hx' : x'.length % 16 = ct.length % 16 := by
    by_cases hc : ct = []
    · subst hc; simp only [x', ite_true, List.length_append, Proof.Gcm.length_zeros, List.length_nil]
      exact Proof.Gcm.length_pad_mod _
    · simp only [x', hc, ite_false, Proof.Gcm.ghashInput_of_ne hc, List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length; omega
  have hlt := Nat.mod_lt a.length (show 16 > 0 by decide)
  have mid : WP isa (.ite .eq firstFlush (.block [])) s₂ fun s₄ => Env c st w sp k7 k8 s₄ ∧ ArgsKeep 7 s₀ s₄ ∧
      blockAt s₄.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
        Absorbed s₄.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x') ∧
      Frame (tFrame st w sp 16) s.mem s₄.mem := by
    refine WP.ite _ (eval_eq' hz₂) (fun ht => ?_) (fun hf₂ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      obtain ⟨i0, v0⟩ := hk₂.at hf hin 0 (by decide) (show 4 * 0 = 0 from rfl)
      obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
          s₃.gpr .r6 = BitVec.ofNat 32 (a.length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
        refine ⟨_, by arun [i0, v0], ?_, ?_, ?_⟩
        · simp only [gpr_setReg, ite_true, v0, and15, ha]
        · intro r a; simp [gpr_setReg, a]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
      have he₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hK₃.sp hK₃.rd hK₃.wr
      have hm₃ : s₃.mem = s.mem := hK₃.mem.trans hm₂
      refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := a) (H := H) ⟨he₃, by rw [hm₃]; exact hH⟩ h6₃))
        fun s₄ hh => ?_
      obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
      have hf₄ := hfl.frame
      rw [hm₃] at hf₄
      refine ⟨hfl.env, (hk₂.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr).frame hf hfl.frame
          (fun r hr => hA r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₄ rd₄ wr₄, hfl.hH, fun hab => ?_, hf₄⟩
      simp only [x', hc, ite_true]
      refine hfl.abs ?_
      rw [hm₃]; subst hc; exact hab
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₂
      refine WP.block_nil ⟨he₂, hk₂, by rw [hm₂]; exact hH, fun hab => ?_, by rw [hm₂]; exact Frame.refl _ _⟩
      simp only [x', hc, ite_false, hm₂]; exact hab
  refine WP.seq (WP.mono mid fun s₄ ⟨he₄, hk₄, hH₄, hab₄, hf₄⟩ => ?_)
  -- the arguments of `absorb`
  obtain ⟨i4, v4⟩ := hk₄.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5', v5'⟩ := hk₄.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i2', v2'⟩ := hk₄.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa textArgs s₄ = some s₅ ∧
      s₅.gpr .r4 = arg s₀ 4 ∧ s₅.gpr .r5 = arg s₀ 5 ∧ s₅.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5', v5', i2', v2'], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v4]
    · simp [gpr_setReg, v5']
    · simp only [gpr_setReg, ite_true, v2', and15]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  have hrd₅ : s₅.rd = s.rd := hk₅.rd.trans hk.rd.symm
  have hwr₅ : s₅.wr = s.wr := hk₅.wr.trans hk.wr.symm
  have hai : AbsIn c st w sp k7 k8 16 H x' (arg s₀ 4) (arg s₀ 5).toNat s₅ :=
    ⟨he₅, h4₅, by rw [h5₅]; simp, by rw [h6₅, hx', lowTo_mod16 hP], hd.of_eq hrd₅ hwr₅, by rw [hK₅.mem]; exact hH₄⟩
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) hai)) fun s₆ hh => ?_
  obtain ⟨ho, rd₆, wr₆, sp₆⟩ := hh
  have hdat : bytesAt s₅.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat =
      bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat := by
    rw [hK₅.mem]
    exact bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hd.st.sub_right (Lay.stSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.stk.symm) (by have := hd.lt; omega)
  have hne : bytesAt s.mem (State.addr (arg s₀ 4)) (arg s₀ 5).toNat ≠ [] := by
    intro e; have := congrArg List.length e; rw [length_bytesAt] at this; exact h0 (by simpa using this)
  refine ⟨ho.env, hk₅.frame hf ho.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₆ rd₆ wr₆, ?_, ?_, ?_⟩
  · rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl)), hK₅.mem, hH₄]
  · intro hab
    have := ho.abs (by rw [hK₅.mem]; exact hab₄ hab)
    rw [hdat] at this
    rw [Proof.Gcm.ghashInput_append _ _ _ hne]
    exact this
  · rw [hK₅.mem] at ho
    exact (t_taFrame hf₄).trans (abs_taFrame ho.frame)

end

end VG.Proof.AesGcm.Arm
