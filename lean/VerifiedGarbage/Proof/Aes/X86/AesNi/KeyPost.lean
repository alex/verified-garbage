import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyContext
import VerifiedGarbage.TCB.X86.Target

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyP keyLen ekSchP ekSchR ekRetR)

/-- The stored doublewords are the shared specification's byte schedule. -/
theorem KeyDone.post {s₀ entry s : State} {nk : Nat} (hd : KeyDone s₀ entry nk s)
    (hn : 0 < nk) (hl : keyLen s₀ = 4 * nk) :
    Proof.Aes.expandKeyX86.post s₀ s := by
  change Spec.Aes.bytesAt s.mem ((ekSchP s₀).setWidth 64)
      (16 * (Spec.Aes.rounds (keyLen s₀ / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem ((keyP s₀).setWidth 64) (keyLen s₀))
  rw [hl, show 4 * nk / 4 = nk by omega, expandKey_eq _ _ hn]
  have hlen : 16 * (Spec.Aes.rounds nk + 1) = 4 * (4 * (nk + 7)) := by
    simp only [Spec.Aes.rounds]; omega
  rw [hlen, bytesAt_eq _ _ _ _ hd.words]
  rfl

/-- Caller-saved-only key expansion preserves the cdecl registers and return slot. -/
theorem KeyDone.abi {s₀ entry s : State} {nk : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (hd : KeyDone s₀ entry nk s) : abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [hd.gpr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hs.callee _ (by decide) (by decide) (by decide)
  · exact hd.frame.readW (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r; exact hp.rS) (by decide)

end VG.Proof.Aes.X86.AesNi
