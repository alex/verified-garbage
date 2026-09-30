import VerifiedGarbage.Proof.MlKem1024.X86.KeyGenFin

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_keygen`

Untrusted: everything here is checked by Lean. The body is the start
(`KeyGenG.lean`), `ŝ` and `ê` (`KeyGenPrf.lean`), the rows of `t̂`
(`KeyGenRow.lean`) and the keys (`KeyGenFin.lean`). If every `SampleNTT`
succeeded (`kg4ACC` is 1), `samp_bound` gives one bound on their iterations,
within which K-PKE.KeyGen succeeds with the matrix sampled
(`kpkeKeyGen1024_some`); if one failed within `minIterations`, K-PKE.KeyGen
fails with that bound (`kpkeKeyGen1024_none`). Two runs with the same
pointers and `ρ` leak the same: the contract lets the function leak `ρ`.
-/

namespace VG.Proof.MlKem1024.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem body_piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Done kg4Body :=
  start_piece <| prfs_piece <| rows_piece fin_piece |>.mono (fun _ _ _ h =>
    ⟨h.ctx, h.rho, h.se, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

theorem piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done s₀) s₀ s')
    Impl.MlKem1024.X86.keyGen :=
  topLeaf (NoSp.of_all (by decide +kernel)) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- Every sample, within one bound. -/
theorem samples {s₀ s : State} (h : Done s₀ s) (e : accV s₀ s = 1) :
    ∃ M, ∀ i < 4, ∀ j < 4, sampleNTT M (matSeed (kgRho1024 (d s₀)) i j) = some (aM s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range 16).map fun k => (mS s₀ k, aM s₀ (k / 4) (k % 4))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mS s₀ k) (sv (mS s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mS s₀ (4 * i + j), aM s₀ ((4 * i + j) / 4) ((4 * i + j) % 4))
    (List.mem_map.mpr ⟨4 * i + j, List.mem_range.mpr (by omega), rfl⟩)
  rw [mS_eq s₀ hj, show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at r
  exact r

/-- The postcondition, from the final state of the body. -/
theorem post {s₀ s : State} (hp : TPre Y s₀) (h : Done s₀ s) :
    Outcome (fun iters => keyGenInternal mlKem1024 iters (d s₀) (z s₀)) (accV s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 1568⟩) 1568, bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 3168⟩) 3168) := by
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    refine .inr ⟨e, ?_⟩
    show keyGenInternal mlKem1024 minIterations (d s₀) (z s₀) = none
    rw [keyGenInternal1024, kpkeKeyGen1024_none (i := k / 4) (j := k % 4) (by omega) (by omega) hn]
    rfl
  · obtain ⟨M, hM⟩ := samples h e
    refine .inl ⟨e, M, ?_⟩
    show keyGenInternal mlKem1024 M (d s₀) (z s₀) = _
    rw [keyGenInternal1024, kpkeKeyGen1024_some hM, ek_full hp h.toF (by decide) e, dk_full hp h.toF e]
    rfl

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.keyGen (Spec.MlKem1024.keyGenContract X86.abi 88) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [d, z, addr0, ez, show Buf.addr s₀ ⟨1, 0, 1568⟩ = (arg s₀ 1).setWidth 64 from addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, 3168⟩ = (arg s₀ 2).setWidth 64 from addr0 s₀ 2] at r
    exact r
  · let st := satState satMem [⟨0, 64⟩]
      [⟨0x100, 1568⟩, ⟨0x1000, 3168⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.KeyGen
