import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallLoop

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_sample_in_ball`

Untrusted: everything here is checked by Lean. The SHAKE256 output, `c`
zeroed, the setup and the loop (`Ball.lean`, `BallLoop.lean`) leave the
state of `SampleInBall`'s loop over the 264 bytes after the sign bits
(`ballFold`) at `c` and `i` in `edi`; the function returns `i >> 8`, and
`sampleInBall_some` and `sampleInBall_none` (`Proof/MlDsa/Sample/Ball.lean`)
give the contract. Two runs with the same pointers and `c̃` leak the same
(`QPub`): the contract lets the function leak `c̃`.
-/

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (bZero bSetup bBody retJ sponge argOp)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly)

/-- The end: `i >> 8` in `eax`. -/
structure Fin (s₀ s : State) : Prop extends BI s₀ 264 (S' s₀ 264) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((S' s₀ 264).2 / 256)

theorem fin_piece : Piece QPre QPub (fun s₀ s => BI s₀ 264 (S' s₀ 264) s) Fin (.block (retJ .edi)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl : (S' s₀ 264).2 ≤ 256 := st_le _ _ _
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ecx], by rw [g _ (by decide), h.ebp], by rw [g _ (by decide), h.edi],
    by rw [o.mem]; exact h.poly, by rw [o.mem]; exact h.lo, by rw [o.mem]; exact h.hi⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.edi]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (S' s₀ 264).2 < 2 ^ 32 by omega)])

theorem main_piece : Piece QPre QPub (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 4 136 (.mem (argOp 1)) 272) <|
      .seq bZero <| .seq (.block bSetup) <| .seq (.loop bBody .ne) (.block (retJ .edi))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h.1) <|
    Piece.seq zero_piece <| Piece.seq setup_piece <| Piece.seq loop_piece fin_piece

theorem piece : Piece QPre QPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.sampleInBall :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem QPre.of {s₀ : State} (h : (Spec.MlDsa.sampleInBallContract X86.abi 56).pre s₀) : QPre s₀ := by
  sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  have hl : (arg s₀ 1).toNat < 136 := by
    simp only [Spec.MlDsa.ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h22
    omega
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hl⟩, h22⟩

theorem S'_all (s₀ : State) : S' s₀ 264 = ballFold (τ s₀) (H (L.Msg s₀) 272) := by
  simp only [S', st, ballFold]
  rw [List.take_of_length_le (by rw [List.length_drop, Xb_length])]

theorem toRq_getElem! (v : IPoly) {i : Nat} (hi : i < n) : (Spec.MlDsa.toRq v)[i]! = ofInt v[i]! := by
  rw [getElem!_pos _ i hi, getElem!_pos _ i hi]
  simp only [Spec.MlDsa.toRq, Vector.getElem_map]

/-- Memory with the arguments `0`, `32`, `39`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 32 else if a = 0x500c then 39 else if a = 0x5011 then 1 else if a = 0x5015 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.sampleInBall (Spec.MlDsa.sampleInBallContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => QPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, ?_⟩
    · match i, hi with
      | 0, _ => exact e₃
      | 1, _ => exact e₄
      | 2, _ => exact e₅
      | 3, _ => exact e₆
      | 4, _ => exact e₇
    · exact RejNtt.map_toNat_inj e₂
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl : (S' s₀ 264).2 ≤ 256 := st_le _ _ _
    have hp : Spec.MlDsa.PolyIs s.mem (L.aA s₀) (Spec.MlDsa.toRq (S' s₀ 264).1) :=
      polyIs_of_coeffAt fun i hi => by rw [hfin.poly i (by simp only [n] at hi; omega), toRq_getElem! _ hi]
    rw [S'_all] at hl hp
    rw [S'_all]
    by_cases e : (ballFold (τ s₀) (H (L.Msg s₀) 272)).2 = 256
    · rw [e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (τ s₀) 272 (L.Msg s₀)).map Spec.MlDsa.toRq =
        some (Spec.MlDsa.polyAt s.mem (L.aA s₀))
      rw [sampleInBall_some _ (by decide) e, hp.2]
      rfl
    · rw [Nat.div_eq_of_lt (by omega)]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), .inr ⟨rfl, ?_⟩⟩
      show (Spec.MlDsa.sampleInBall (τ s₀) Spec.MlDsa.minBounds.ball (L.Msg s₀)).map Spec.MlDsa.toRq = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) e]
      rfl
  · let st := satState satMem [⟨0, 32⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.Ball
