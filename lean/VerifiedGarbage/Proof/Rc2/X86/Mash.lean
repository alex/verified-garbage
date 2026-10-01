import VerifiedGarbage.Proof.Rc2.X86.MashSteps

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 32).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 4294967296 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 4294967296 by have := x.isLt; omega)]

def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mashSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat)
    (v : Spec.Rc2.State) : mashSpec d k i v = v.set! i
      (mashResult d (v.getD i 0) (k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)) := by
  cases d <;> rfl

theorem mash_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s) (i : Nat) (hi : i < 4) :
    WP isa (.block (mash d i)) s (fun s' =>
      MemWords s'.mem (wordBase s') (mashSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) i v) ∧
      RoundFrame s s') := by
  rw [mash, List.append_assoc, List.append_assoc, WP.block_append_iff]
  apply WP.mono (mashInput_ok s v hv env i)
  intro s₁ ⟨index₁, key₁, keep₁⟩
  rw [WP.block_append_iff]
  apply WP.mono (keyLookup_ok s₁ (by rw [key₁]; exact env.keyFit)
    (by rw [keep₁.rd, keep₁.wr, key₁]; exact env.keyRead))
  intro s₂ h₂
  have k₁ : Keep roundWrites s s₁ := keep₁.weaken (by decide)
  have k₂ : Keep roundWrites s₁ s₂ := h₂.2.weaken (by decide)
  have keep := k₁.trans k₂
  have frame := RoundFrame.of_keep keep
  have env₂ := frame.env env
  have words₂ : MemWords s₂.mem (wordBase s₂) v := by rw [keep.mem, frame.base]; exact hv
  have key₂ : s₂.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))).getD
      ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0).setWidth 32 := by
    rw [h₂.1, keep₁.mem, key₁, index₁, indexWord]
  rw [WP.block_append_iff]
  apply WP.mono (mashAdjust_ok d s₂ v words₂ env₂ i hi _ key₂)
  intro s₃ h₃
  have k₃ : Keep roundWrites s₂ s₃ := h₃.2.weaken (by decide)
  have frame₃ := frame.trans (RoundFrame.of_keep k₃)
  obtain ⟨s₄, run₄, mem₄, frame₄⟩ := storeWord32_ok s₃ .edx i hi (frame₃.env env)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, frame₃.trans frame₄⟩
  rw [frame₄.base, frame₃.base, mem₄, frame₃.base, h₃.1, h₃.2.mem, keep.mem, mashSpec_eq]
  exact hv.update i hi _

end VG.Proof.Rc2.X86
