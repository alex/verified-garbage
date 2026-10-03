import VerifiedGarbage.Proof.TripleDes.X86.Ready

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (.seq (pass c₀ d₀) (.seq (pass c₁ d₁) (pass c₂ d₂))) s
      (fun t => WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        Ready keys base t ∧ Stable s t) := by
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s x c₀ h₀ d₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s₁ _ c₁ h₁ d₁ hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (pass_word_ok keys base s₂ _ c₂ h₂ d₂ hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1, hs₁.2.2.trans (hs₂.2.2.trans hs₃.2.2)⟩

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  cases direction
  · exact threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt hready hword
  · exact threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt hready hword

end VG.Proof.TripleDes.X86
