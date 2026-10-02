import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt

/-!
# AES-GCM on ARMv7: `textAbsorb` is constant time

Untrusted: everything here is checked by Lean. Two runs from initial states
`s₀` and `s₀'` with the same stack arguments: the blocks read them as
public, and `flush` and `absorb` are constant time by `flush_ct` and
`absorb_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `textAbsorb` needs, in a run from `s₀`. -/
def TA (s₀ : State) (c st w sp : BitVec 32) (s : State) : Prop :=
  ∃ k7 k8, Env c st w sp k7 k8 s ∧ ArgsKeep 7 s₀ s ∧ DataOk st w sp s (arg s₀ 4) (arg s₀ 5).toNat

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

/-- `flush 16`, for one run, kept to what `textAbsorb` needs. -/
theorem ta_flush {s₀ s : State} (h : TA s₀ c st w sp s) {q : Nat} (hq : q < 16) (h6 : s.gpr .r6 = BitVec.ofNat 32 q)
    (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hA : ∀ r ∈ taFrame st w sp, (args s₀ 7).Disjoint r) :
    WP isa (flush 16) s (TA s₀ c st w sp) := by
  obtain ⟨k7, k8, he, hk, hd⟩ := h
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, k8, fl.env, hk.frame hf fl.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp' rd wr, hd.of_eq rd wr⟩

theorem textAbsorb_rel {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < 7, arg s₀ i = arg s₀' i) (hw : ∀ r ∈ s₀.wr, (args s₀ 7).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (args s₀' 7).Disjoint r) (hin : args s₀ 7 ∈ s₀.rd) (hin' : args s₀' 7 ∈ s₀'.rd)
    (hA : ∀ r ∈ taFrame st w sp, (args s₀ 7).Disjoint r) (hA' : ∀ r ∈ taFrame st w sp, (args s₀' 7).Disjoint r) :
    RelCT isa (fun a b => TA s₀ c st w sp a ∧ TA s₀' c st w sp b) textAbsorb fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * 7 ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, ArgsKeep 7 s₀ s → ArgsKeep 7 s₀' s' →
      VG.Arm.Taint.Agree (argTaint [] (4 * 7)) s s' := fun k k' =>
    k.agree k' hsp hf ha hw hw' (by simp)
  -- the length of the data
  let G₁ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.z = decide ((arg t₀ 5).toNat = 0)
  have run₁ : ∀ {t₀ s : State}, TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block [.ldrSp .r5 20, .cmp .r5 (imm 0)]) s (G₁ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨i5, v5⟩ := hk.at f i 5 (by decide) (show 4 * 5 = 20 from rfl)
    refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, v5]; exact z_sub0 _
  have a := rel_agree (F := TA s₀ c st w sp) (F' := TA s₀' c st w sp) (G := G₁ s₀) (G' := G₁ s₀')
    (argTaint [] (4 * 7)) (c := .block [.ldrSp .r5 20, .cmp .r5 (imm 0)])
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₁ h hf hin) (fun s h => run₁ h hf' hin')
  refine a.seq (rel_ite (decide ((arg s₀ 5).toNat = 0)) (fun s h => h.2) (fun s h => by rw [h.2, ha 5 (by decide)])
    (fun _ => rel_skip) fun _ => ?_)
  -- whether there is text so far
  let G₂ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.z = decide ((arg t₀ 3 ++ arg t₀ 2).toNat = 0)
  have run₂ : ∀ {t₀ s : State}, G₁ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block tlenZero) s (G₂ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by decide) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by decide) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl, hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [z_sub0]
    exact decide_eq_decide.mpr (or_zero_iff _ _)
  have b := rel_agree (F := G₁ s₀) (F' := G₁ s₀') (G := G₂ s₀) (G' := G₂ s₀')
    (argTaint [] (4 * 7)) (c := .block tlenZero)
    (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₂ h hf hin) (fun s h => run₂ h hf' hin')
  refine b.seq ?_
  -- the additional data padded, before the first text
  have ff : ∀ {t₀ : State}, t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      (∀ r ∈ taFrame st w sp, (args t₀ 7).Disjoint r) →
      ∀ s, G₂ t₀ s → WP isa (.ite .eq firstFlush (.block [])) s (TA t₀ c st w sp) := fun {t₀} f i hA₀ s ⟨hs, hz⟩ => by
    refine WP.ite _ (eval_eq' hz) (fun _ => ?_) (fun _ => WP.block_nil hs)
    obtain ⟨k7, k8, he, hk, hd⟩ := hs
    obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
    refine WP.seq (WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩)
    refine ta_flush L ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩ (q := (arg t₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)) ?_ f hA₀
    simp only [gpr_setReg, ite_true, v0, and15]
  have cF : RelCT isa (fun a b => G₂ s₀ a ∧ G₂ s₀' b) (.ite .eq firstFlush (.block [])) fun _ _ => True := by
    refine rel_ite (decide ((arg s₀ 3 ++ arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by decide), ha 2 (by decide)]) (fun _ => ?_) (fun _ => rel_skip)
    let G₃ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 0).toNat % 16)
    have run₃ : ∀ {t₀ s : State}, G₂ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
        WP isa (.block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)]) s (G₃ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
      obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, k8, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
        hd.of_eq rfl rfl⟩, ?_⟩
      simp only [gpr_setReg, ite_true, v0, and15]
    have c₁ := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (G := G₃ s₀) (G' := G₃ s₀')
      (argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)])
      (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
      (fun s h => run₃ h hf hin) (fun s h => run₃ h hf' hin')
    exact c₁.seq (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, h6⟩)
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, by rw [h6, ha 0 (by decide)]⟩))
  refine (rel_wp cF (ff hf hin hA) (ff hf' hin' hA')).seq ?_
  -- the arguments of `absorb`
  let G₄ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.gpr .r4 = arg t₀ 4 ∧ s.gpr .r5 = arg t₀ 5 ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 2).toNat % 16)
  have run₄ : ∀ {t₀ s : State}, TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block textArgs) s (G₄ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run hk f i
    exact WP.of_runBlock ⟨s', run, ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      hk.of_eq hK.mem hK.sp hK.rd hK.wr, hd.of_eq hK.rd hK.wr⟩, h4, h5, h6⟩
  have d := rel_agree (F := TA s₀ c st w sp) (F' := TA s₀' c st w sp) (G := G₄ s₀) (G' := G₄ s₀')
    (argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₄ h hf hin) (fun s h => run₄ h hf' hin')
  refine d.seq (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 4) (n := (arg s₀ 5).toNat)
    (q := (arg s₀ 2).toNat % 16) (Nat.mod_lt _ (by decide))) ?_ ?_)
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, h4, by rw [h5]; simp, by rw [h6]; simp, hd, rfl⟩⟩
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    rw [← ha 4 (by decide), ← ha 5 (by decide)] at hd
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, by rw [h4, ha 4 (by decide)], by rw [h5, ha 5 (by decide)]; simp,
        by rw [h6, ha 2 (by decide)]; simp, hd, rfl⟩⟩

end

end VG.Proof.AesGcm.Arm
