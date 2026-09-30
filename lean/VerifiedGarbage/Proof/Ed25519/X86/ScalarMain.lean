import VerifiedGarbage.Proof.Ed25519.X86.ScalarContract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_correct {s : State} (h : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hp, hi, ho⟩ := scalarReduce_pre h
  simp only [scalarReduce, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.mono (loadInput_ok hp hi hu (by decide) (dst := 128) (by decide) (by decide) (by decide))
    fun v ⟨hv, words, _⟩ => ?_
  refine WP.seq (WP.mono (scalarEngine_ok (hv.ctx hp.fit hp.wr)) fun w ⟨kw, fw, vw⟩ => ?_)
  have hw := hv.scalarEngine hp.fit kw fw
  refine WP.mono (finishWords_ok hp ho hw (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, vw, Spec.Ed25519.scalarReduce, scalarInput_num v.mem hp.fit]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  apply congrArg (· % Spec.Ed25519.L)
  have ew : num (fun k => wv v.mem (arg s 2) (128 + 4 * k)) 16 =
      num (fun k => wv s.mem (arg s 1) (0 + 4 * k)) 16 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (words k hk)
  rw [ew, ← decode_words s.mem 16 (by have := hi.fit; omega_using [this]), addr_zero]
end VG.Proof.Ed25519.X86
