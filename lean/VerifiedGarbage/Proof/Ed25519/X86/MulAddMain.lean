import VerifiedGarbage.Proof.Ed25519.X86.MulAddContract
import VerifiedGarbage.Proof.Ed25519.X86.MulAddSetup
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_correct {s : State} (h : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hp, hA, hB, hC, ho⟩ := scalarMulAdd_pre h
  simp only [scalarMulAdd, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.block_append (WP.mono (scalarMulInputs_ok hp hA hB hC hu) fun v ⟨hv, evA, evB, evC⟩ => ?_)
  refine WP.mono (scalarWideMul_ok (hv.ctx hp.fit hp.wr)) fun w ⟨kw, fw, ew⟩ => ?_
  have hw := hv.of_offset hp.fit (Keep.scalar kw) fw (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (scalarEngine_ok (hw.ctx hp.fit hp.wr)) fun z ⟨kz, fz, ez⟩ => ?_)
  have hz := hw.scalarEngine hp.fit kz fz
  refine WP.mono (finishWords_ok hp ho hz (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ez, scalarInput_num w.mem hp.fit, ew, evA, evB, evC, Spec.Ed25519.scalarMulAdd]
  rw [Nat.add_comm]
end VG.Proof.Ed25519.X86
