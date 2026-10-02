import VerifiedGarbage.Proof.MlKem.X86.KeyGenFin

/-!
# ML-KEM on x86 (32-bit): the body of key generation

The body is the start (`KeyGenG.lean`), `ŝ` and `ê` (`KeyGenPrf.lean`), the
rows of `t̂` (`KeyGenRow.lean`) and the keys (`KeyGenFin.lean`). If every
`SampleNTT` succeeded (`kgACC` is 1), `samp_bound` gives one bound on their
iterations, within which K-PKE.KeyGen succeeds with the matrix sampled
(`KPke.kpkeKeyGen_some`); if one failed within `minIterations`, K-PKE.KeyGen
fails with that bound (`KPke.kpkeKeyGen_none`) (`post`). Two runs with the
same pointers and `ρ` leak the same: the contract lets the function leak `ρ`.
Each parameter set's contract implies `TPre (Y L)` and its public data
(`Proof/MlKem/X86/KeyGen.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay}

theorem body_piece [GOK L] [PrfOK L] [KgRowOK L] [FinOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) (Done L) (kgBody L) :=
  start_piece <| prfs_piece <| rows_piece fin_piece |>.mono (fun _ _ _ h =>
    ⟨h.ctx, h.rho, h.se, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

theorem piece [GOK L] [PrfOK L] [KgRowOK L] [FinOK L] (hsp : NoSp (kgBody L)) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done L s₀) s₀ s')
      (leaf (kgBody L)) :=
  topLeaf hsp (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- Every sample, within one bound. -/
theorem samples {s₀ s : State} (h : Done L s₀ s) (e : accV L s₀ s = 1) :
    ∃ M, ∀ i < L.p.k, ∀ j < L.p.k, sampleNTT M (matSeed (KPke.kgRho L.p (d s₀)) i j) = some (aM L s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range (L.p.k * L.p.k)).map fun k =>
      (mS L s₀ k, aM L s₀ (k / L.p.k) (k % L.p.k))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mS L s₀ k) (sv (mS L s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mS L s₀ (L.p.k * i + j), aM L s₀ ((L.p.k * i + j) / L.p.k) ((L.p.k * i + j) % L.p.k))
    (List.mem_map.mpr ⟨L.p.k * i + j, List.mem_range.mpr (idx_lt hi hj), rfl⟩)
  rw [mS_eq s₀ hj, idx_div hj, idx_mod hj] at r
  exact r

/-- The postcondition, from the final state of the body. -/
theorem post [FinOK L] (hη : L.p.η₁ = 2) {s₀ s : State} (hp : TPre (Y L) s₀) (h : Done L s₀ s) :
    Outcome (fun iters => keyGenInternal L.p iters (d s₀) (z s₀)) (accV L s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen,
        bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen) := by
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega
    refine .inr ⟨e, ?_⟩
    show keyGenInternal L.p minIterations (d s₀) (z s₀) = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (i := k / L.p.k) (j := k % L.p.k)
      (Nat.div_lt_of_lt_mul hk) (Nat.mod_lt _ hk0) hn]
    rfl
  · obtain ⟨M, hM⟩ := samples h e
    refine .inl ⟨e, M, ?_⟩
    show keyGenInternal L.p M (d s₀) (z s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some hη hM, ek_full hp h.toF (by omega) e, dk_full hp h.toF e]
    rfl

end VG.Proof.MlKem.X86.KeyGen
