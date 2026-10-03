import VerifiedGarbage.Proof.Argon2.AArch64.Initial
import VerifiedGarbage.Proof.Argon2.AArch64.InitialBlocksCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FixedCT

/-! Public input metadata survives every hash call without relating input bytes. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

structure Ready (s : State) : Prop where
  space : Space s
  inputs : ∀ input ∈ inputs, InputReady s input.1 input.2

theorem Ready.keeps {s t : State} (h : Ready s) (k : Keeps s t) : Ready t :=
  ⟨h.space.keeps k, fun p hp => (h.inputs p hp).keeps k⟩

structure Related (s t : State) : Prop where
  left : Ready s
  right : Ready t
  bp : s.gpr .x19 = t.gpr .x19
  bx : s.gpr .x24 = t.gpr .x24
  sp : s.sp = t.sp
  words : ∀ d ∈ slots, wordAt s d = wordAt t d

theorem Related.keeps {s₁ s₂ t₁ t₂ : State} (h : Related s₁ s₂)
    (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related t₁ t₂ := by
  refine ⟨h.left.keeps k₁, h.right.keeps k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.x19, k₂.x19, h.bp]
  · rw [k₁.x24, k₂.x24, h.bx]
  · rw [k₁.sp, k₂.sp, h.sp]
  · intro d hd
    have bound : ∀ d ∈ slots, d + 8 ≤ 272 := by decide
    rw [h.left.space.word_keeps k₁ d (bound d hd), h.right.space.word_keeps k₂ d (bound d hd)]
    exact h.words d hd

def RelatedRegs (rs : List Reg) (s t : State) : Prop :=
  Related s t ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem hash_keeps_rel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (saved : ∀ r ∈ rs, r ∈ preserved ∧ r ≠ .x30)
    (ct : RelCT isa P c (fun _ _ => True))
    (pre : ∀ s t, P s t → RelatedRegs rs s t)
    (wp : ∀ s t, P s t → WP isa c s (HPrime.Keeps s) ∧ WP isa c t (HPrime.Keeps t)) :
    RelCT isa P c (RelatedRegs rs) := by
  apply (ct.wpDep wp).mono (fun _ _ h => h)
  rintro a b ⟨_, s, t, hp, ha, hb⟩
  have h := pre s t hp
  refine ⟨h.1.keeps (Keeps.of_hash ha) (Keeps.of_hash hb), ?_⟩
  intro r hr
  rw [ha.regs r (saved r hr).1 (saved r hr).2, hb.regs r (saved r hr).1 (saved r hr).2]
  exact h.2 r hr

theorem finalize_ready {s : State} (h : Ready s) : HPrime.FinalizeReady s :=
  ⟨h.space.stackMinimum, h.space.work, h.space.stackWork⟩

end VG.Proof.Argon2.AArch64.Initial
