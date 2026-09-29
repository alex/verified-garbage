import VerifiedGarbage.Proof.MlKem.X86.KeyGenFin

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_keygen`

Untrusted: everything here is checked by Lean. The body is the start
(`KeyGenG.lean`), `ŝ` and `ê` (`KeyGenPrf.lean`), the rows of `t̂`
(`KeyGenRow.lean`) and the keys (`KeyGenFin.lean`). If every `SampleNTT`
succeeded (`kgACC` is 1), `samp_bound` gives one bound on their iterations,
within which K-PKE.KeyGen succeeds with the matrix sampled
(`kpkeKeyGen768_some`); if one failed within `minIterations`, K-PKE.KeyGen
fails with that bound (`kpkeKeyGen768_none`). Two runs with the same
pointers and `ρ` leak the same: the contract lets the function leak `ρ`.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem body_piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Done kgBody :=
  start_piece <| prfs_piece <| rows_piece fin_piece |>.mono (fun _ _ _ h =>
    ⟨h.ctx, h.rho, h.se, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

theorem piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done s₀) s₀ s')
    Impl.MlKem.X86.keyGen :=
  topLeaf (NoSp.of_all (by decide +kernel)) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- Every sample, within one bound. -/
theorem samples {s₀ s : State} (h : Done s₀ s) (e : accV s₀ s = 1) :
    ∃ M, ∀ i < 3, ∀ j < 3, sampleNTT M (matSeed (kgRho (d s₀)) i j) = some (aM s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range 9).map fun k => (mS s₀ k, aM s₀ (k / 3) (k % 3))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mS s₀ k) (sv (mS s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mS s₀ (3 * i + j), aM s₀ ((3 * i + j) / 3) ((3 * i + j) % 3))
    (List.mem_map.mpr ⟨3 * i + j, List.mem_range.mpr (by omega), rfl⟩)
  rw [mS_eq s₀ hj, show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at r
  exact r

/-- The postcondition, from the final state of the body. -/
theorem post {s₀ s : State} (hp : TPre Y s₀) (h : Done s₀ s) :
    Outcome (fun iters => keyGenInternal mlKem768 iters (d s₀) (z s₀)) (accV s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 1184⟩) 1184, bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 2400⟩) 2400) := by
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    refine .inr ⟨e, ?_⟩
    show keyGenInternal mlKem768 minIterations (d s₀) (z s₀) = none
    rw [keyGenInternal768, kpkeKeyGen768_none (i := k / 3) (j := k % 3) (by omega) (by omega) hn]
    rfl
  · obtain ⟨M, hM⟩ := samples h e
    refine .inl ⟨e, M, ?_⟩
    show keyGenInternal mlKem768 M (d s₀) (z s₀) = _
    rw [keyGenInternal768, kpkeKeyGen768_some hM, ek_full hp h.toF (by decide) e, dk_full hp h.toF e]
    rfl

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.keyGen (keyGenContract X86.abi 88) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [d, z, addr0, ez, show Buf.addr s₀ ⟨1, 0, 1184⟩ = (arg s₀ 1).setWidth 64 from addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, 2400⟩ = (arg s₀ 2).setWidth 64 from addr0 s₀ 2] at r
    exact r
  · obtain ⟨st, hst⟩ : ∃ st, st = satState satMem [⟨0, 64⟩]
        [⟨0x100, 1184⟩, ⟨0x1000, 2400⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩] := ⟨_, rfl⟩
    have a0 : arg st 0 = 0 := by rw [hst]; decide
    have a1 : arg st 1 = 0x100 := by rw [hst]; decide
    have a2 : arg st 2 = 0x1000 := by rw [hst]; decide
    have a3 : arg st 3 = 0x10000 := by rw [hst]; decide
    have e : argAddr st 0 = 0x5004 := by rw [hst]; decide
    have esp : st.gpr .esp = 0x5000 := by rw [hst]; rfl
    refine ⟨st, ?_⟩
    sig_pre [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e, esp]
    refine ⟨by decide, by decide, by rw [hst]; rfl, by rw [hst]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlKem.X86.KeyGen
