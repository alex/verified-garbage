import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCheckpoints
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyTables

/-! Load checked constants into the same checkpoint layout as runtime doubling. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem baseCheckpointStore_ok {s : State} {base : Addr} (hs : Scratch s base)
    (i : Nat) (hi : i < 16) :
    WP isa (.block (baseCheckpointStore i)) s fun t =>
      PowersKeep base (1280 + 128 * i) 128 s t ∧
      tablePoint t.mem base (1280 + 128 * i) = baseCheckpoint i ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [baseCheckpointStore, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs (constPointOps (baseCheckpoint i))) fun a ⟨ka, av⟩ => ?_
  refine WP.mono (pointTableWrite_ok (hs.of_keep ka) (1280 + 128 * i)
    (by omega) (by omega)) fun t ⟨kt, tv, te⟩ => ?_
  refine ⟨(PowersKeep.of_keep ka).trans kt, ?_, ?_⟩
  · rw [tv, av, constPoint_eval]
  · rw [te, av]; rfl

theorem baseCheckpointStores_ok {s : State} {base : Addr} (hs : Scratch s base)
    (n : Nat) (hn : n ≤ 16) :
    WP isa (.block (baseCheckpointStores n)) s fun t =>
      PowersKeep base 1280 (128 * n) s t ∧
      (∀ i < n, tablePoint t.mem base (1280 + 128 * i) = baseCheckpoint i) ∧
      env t.mem base 16 = env s.mem base 16 := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨PowersKeep.refl _ _ _ _, by omega, rfl⟩
  | succ n ih =>
    rw [baseCheckpointStores, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      WP.block_append_iff]
    refine WP.mono (ih hs (by omega)) fun a ⟨ka, av, ad⟩ => ?_
    refine WP.mono (baseCheckpointStore_ok (ka.scratch hs) n (by omega)) fun t ⟨kt, tv, td⟩ => ?_
    refine ⟨(ka.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)), ?_, td.trans ad⟩
    intro i hi
    by_cases he : i = n
    · subst i; exact tv
    · rw [kt.mem.point (by omega) (Or.inl (by omega)) (by omega)]
      exact av i (by omega)

end VG.Proof.Ed25519.X86_64
