import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.MulAddWide

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem copied_fe {s₀ t : State} {p x : BitVec 32} {dst : Nat}
    (hp : p.toNat + 32 ≤ 2 ^ 32)
    (hw : ∀ k < 8, wd t.mem x (dst + 4 * k) = wd s₀.mem p (4 * k)) :
    fe t.mem x dst = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) 32) := by
  have ew : fe t.mem x dst = num (fun k => wv s₀.mem p (0 + 4 * k)) 8 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (hw k hk)
  rw [ew, ← decode_words s₀.mem 8 (by omega_using [hp]), addr_zero]

theorem scalarMulInputs_ok {s₀ s : State} (hp : ScratchPre s₀ 4 5)
    (hA : InputPre s₀ 4 2 8) (hB : InputPre s₀ 4 3 8) (hC : InputPre s₀ 4 1 8)
    (hs : Saved s₀ (arg s₀ 4) s) :
    WP isa (.block scalarMulInputs) s fun t => Saved s₀ (arg s₀ 4) t ∧
      fe t.mem (arg s₀ 4) 256 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 288 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 320 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) := by
  have he : scalarMulInputs =
      (([.mov .esi (.mem (at_ .esp 12))] : List Instr) ++ copyWords 256 8) ++
      ((([.mov .esi (.mem (at_ .esp 16))] : List Instr) ++ copyWords 288 8) ++
      (([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 320 8)) := by
    simp only [scalarMulInputs, List.append_assoc]
  rw [he]
  refine WP.block_append (WP.mono (loadInput_ok hp hA hs (by decide) (dst := 256)
    (by decide) (by decide) (by decide)) fun u ⟨hu, wu, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadInput_ok hp hB hu (by decide) (dst := 288)
    (by decide) (by decide) (by decide)) fun v ⟨hv, wv, fv⟩ => ?_)
  refine WP.mono (loadInput_ok hp hC hv (by decide) (dst := 320)
    (by decide) (by decide) (by decide)) fun t ⟨ht, wt, ft⟩ => ?_
  refine ⟨ht, ?_, ?_, copied_fe hC.fit wt⟩
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide)),
      fe_frame1 fv hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hA.fit wu
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hB.fit wv
end VG.Proof.Ed25519.X86
