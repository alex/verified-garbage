import VerifiedGarbage.Proof.TripleDes.Arm.Ready
namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (o₀ o₁ o₂ : Int)
    (e₀ : encodable (BitVec.ofNat 32 o₀.natAbs) = true)
    (e₁ : encodable (BitVec.ofNat 32 o₁.natAbs) = true)
    (e₂ : encodable (BitVec.ofNat 32 o₂.natAbs) = true)
    (p₀ : startPointer (s.gpr .r0) o₀ = keyAddr (componentBase base c₀) d₀ 0)
    (p₁ : startPointer (endPointer (componentBase base c₀) d₀) o₁ = keyAddr (componentBase base c₁) d₁ 0)
    (p₂ : startPointer (endPointer (componentBase base c₁) d₁) o₂ = keyAddr (componentBase base c₂) d₂ 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (.seq (pass o₀ d₀) (.seq (pass o₁ d₁) (pass o₂ d₂))) s
      (fun t => WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c₂) d₂) := by
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s x c₀ h₀ d₀ o₀ e₀ p₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s₁ _ c₁ h₁ d₁ o₁ e₁
    (by rw [hs₁.2.2.2]; exact p₁) hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (pass_word_ok keys base s₂ _ c₂ h₂ d₂ o₂ e₂
    (by rw [hs₂.2.2.2]; exact p₂) hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1,
    hs₁.2.2.1.trans (hs₂.2.2.1.trans hs₃.2.2.1), hs₃.2.2.2⟩

theorem passPointers (base : BitVec 32) :
    startPointer base 0 = keyAddr (componentBase base 0) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 0) .encrypt) 120 = keyAddr (componentBase base 1) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .decrypt) 136 = keyAddr (componentBase base 2) .encrypt 0 ∧
    startPointer base 376 = keyAddr (componentBase base 2) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 2) .decrypt) (-120) = keyAddr (componentBase base 1) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .encrypt) (-136) = keyAddr (componentBase base 0) .decrypt 0 := by
  simp only [startPointer, endPointer, componentBase, keyAddr,
    Int.reduceLT, Int.natAbs_neg, ite_true, ite_false, reduceCtorEq,
    Nat.reduceMul, Nat.reduceSub]
  repeat' constructor <;> bv_omega

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hptr : s.gpr .r0 = base)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t ∧
        t.gpr .r0 = (if direction = .encrypt then base + 384 else base - 8)) := by
  obtain ⟨p₀, p₁, p₂, p₃, p₄, p₅⟩ := passPointers base
  cases direction
  · apply WP.mono (threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt 0 120 136 (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₀) p₁ p₂ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change base + BitVec.ofNat 32 256 + BitVec.ofNat 32 128 = base + BitVec.ofNat 32 384
    rw [Offset.add_ofNat_add_ofNat]
  · apply WP.mono (threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt 376 (-120) (-136) (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₃) p₄ p₅ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change (base + 0) - 8 = base - 8
    exact congrArg (· - (8 : BitVec 32)) (BitVec.add_zero base)
end VG.Proof.TripleDes.Arm
