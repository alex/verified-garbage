import VerifiedGarbage.Proof.Rc2.X86.MixCore
import VerifiedGarbage.Proof.Rc2.X86.RoundFrame

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def mixSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mix k j i v
  | .decrypt => Spec.Rc2.reverseMix k j i v

theorem mixSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : mixSpec d k j i v = v.set! i (mixResult d k j i v) := by
  cases d <;> rfl

theorem mixStep_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s)
    (i j : Nat) (hi : i < 4) (hj : j < 64) :
    WP isa (.block (loadWords ++ mixCore d j i ++
      ([.store (memOp .ebp (wordOff i)) (wordReg i)] : List Instr))) s (fun s' =>
        MemWords s'.mem (wordBase s') (mixSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v) ∧
        RoundFrame s s') := by
  rw [List.append_assoc, WP.block_append_iff]
  apply WP.mono (loadWords_ok s v hv env.scratchFit env.wordRead)
  intro s₁ h₁
  have k₁ : Keep roundWrites s s₁ := h₁.2.weaken (by decide)
  have f₁ := RoundFrame.of_keep k₁
  have e₁ := f₁.env env
  rw [WP.block_append_iff]
  apply WP.mono (mixCore_ok d s₁ v h₁.1 i j hi hj e₁.stackRead e₁.keyFit e₁.keyRead)
  intro s₂ h₂
  have k₂ := keep_mix_round h₂.2
  have f₂ := RoundFrame.of_keep k₂
  have frame := f₁.trans f₂
  have keep := k₁.trans k₂
  obtain ⟨s₃, run₃, mem₃, frame₃⟩ := storeWord32_ok s₂ (wordReg i) i hi (frame.env env)
  refine WP.of_runBlock ⟨s₃, run₃, ?_, frame.trans frame₃⟩
  rw [frame₃.base, frame.base, mixSpec_eq, mem₃, frame.base, h₂.1, keep.mem,
    f₁.schedule env]
  exact hv.update i hi _

end VG.Proof.Rc2.X86
