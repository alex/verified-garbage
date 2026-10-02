import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlKem.Mem

namespace VG.Proof.MlDsa.Sample
open VG
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)
/-- The result of either implementation: whether each seed has 256 coefficients in its first 1008
bytes of output. -/
def rej4Res (m : Mem) (a : Addr) : BitVec 32 :=
  if (List.range 4).all (fun k => (rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) then 1 else 0

theorem seed4_of136 {m m' : Mem} {a a' : Addr} (h : bytesAt m a 136 = bytesAt m' a' 136) {k : Nat} (hk : k < 4) :
    Spec.MlDsa.seed4 m a k = Spec.MlDsa.seed4 m' a' k := by
  unfold Spec.MlDsa.seed4
  rw [← Proof.MlKem.bytesAt_slice m a (show 34 * k + 34 ≤ 136 by omega),
    ← Proof.MlKem.bytesAt_slice m' a' (show 34 * k + 34 ≤ 136 by omega), h]

/-- The result depends only on the 136 bytes of the seeds. -/
theorem rej4Res_congr {m m' : Mem} {a a' : Addr} (h : bytesAt m a 136 = bytesAt m' a' 136) :
    rej4Res m a = rej4Res m' a' := by
  have e : ((List.range 4).all fun k => (rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) =
      ((List.range 4).all fun k => (rnFold [] (G (Spec.MlDsa.seed4 m' a' k) 1008)).length == 256) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun H k hk => by rw [← seed4_of136 h (List.mem_range.mp hk)]; exact H k hk,
      fun H k hk => by rw [seed4_of136 h (List.mem_range.mp hk)]; exact H k hk⟩
  simp only [rej4Res, e]

/-- Within the bound both implementations sample to, so within `maxBounds`'s. -/
theorem rej4Res_max {m : Mem} {a : Addr} (h : rej4Res m a = 1) {k : Nat} (hk : k < 4) {B : Nat} (hB : 1008 ≤ B) :
    (Spec.MlDsa.rejNTTPoly B (Spec.MlDsa.seed4 m a k)).isSome := by
  unfold rej4Res at h
  by_cases hall : ((List.range 4).all fun k => (rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length == 256) = true
  · have hs : (rnFold [] (G (Spec.MlDsa.seed4 m a k) 1008)).length = 256 := by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    rw [Proof.MlDsa.KeyGen.rejNTTPoly_mono hB (rejNTT_some hs)]; rfl
  · rw [ite_eq_right hall] at h; exact absurd h (by decide)

end VG.Proof.MlDsa.Sample
