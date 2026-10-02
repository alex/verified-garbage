import VerifiedGarbage.Proof.MlKem.X86.SampleLoop

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_sample_ntt`

Untrusted: everything here is checked by Lean. The body is the SHAKE128
output of the seed at `scratch` (`SampleSetup.lean`, `SampleCalls.lean`),
then the 280 iterations of the loop (`SampleLoop.lean`), which leave
`sampleAfter [] (xofByte B) 280` at `a` and return whether it has 256
coefficients; `sampleNTT_of_full`, `sampleNTT_none` and `outcome_of_min`
(`Proof/MlKem/KPke.lean`) give the contract. Two runs with the same
pointers and seed leak the same (`Pub`): the contract lets the function
leak the seed.
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem main_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block [.mov .esi (.mem (at_ .esp 28))]) <|
      .seq (zeroSt smpSt) <|
      .seq (.block smpAbsorbArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) <|
      .seq (.block smpPadArgs) <|
      .seq (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) <|
      .seq (.block smpSqueezeArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) <|
      .seq (.block smpLoopInit) <|
      .seq (.loop smpBody .ne) (.block smpEnd)) :=
  Piece.seq ld_piece <| Piece.seq zero_piece <| Piece.seq absArgs_piece <| Piece.seq absorb_call <|
    Piece.seq padArgs_piece <| Piece.seq pad_call <| Piece.seq sqArgs_piece <| Piece.seq squeeze_call <|
    Piece.seq linit_piece <| Piece.seq loop_piece fin_piece

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem.X86.sampleNTT :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨by have := hp.sp; omega, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The coefficients at `a`, when there are 256. -/
theorem poly_eq {s₀ s : State} (h : Loop s₀ 280 (LA (Bs s₀) 280) s) (hl : (LA (Bs s₀) 280).length = 256) :
    Reduced s.mem (aA s₀) ∧ polyAt s.mem (aA s₀) = toPoly (LA (Bs s₀) 280) := by
  have hc : ∀ i < n, coeffAt s.mem (aA s₀) i = cv (LA (Bs s₀) 280) i := fun i hi =>
    h.coef i (by rw [hl]; rw [n_eq] at hi; exact hi)
  have hv : ∀ i < n, (coeffAt s.mem (aA s₀) i).toNat = ((LA (Bs s₀) 280).getD i 0).val := fun i hi => by
    rw [hc i hi, cv, toNat_ofNat32 (by have := ((LA (Bs s₀) 280).getD i 0).isLt; have := q_eq; omega)]
  refine ⟨fun i hi => by rw [hv i hi]; exact ((LA (Bs s₀) 280).getD i 0).isLt, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, toPoly, Vector.getElem_ofFn]
  rw [hv i hi, ofNat_val]

/-- Memory with the arguments `0`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.sampleNTT (sampleNTTContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    exact ⟨e₁, map_toNat_inj e₂, e₃, e₄, e₅⟩
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl := hfin.len
    by_cases e : (LA (Bs s₀) 280).length = 256
    · obtain ⟨hr, hp⟩ := poly_eq hfin.toLoop e
      rw [e]
      refine ⟨fun _ => hr, outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
      rw [hp]
      exact sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact e)
    · rw [Nat.div_eq_of_lt (by omega)]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
      exact sampleNTT_none (by rw [n_eq]; exact e)
  · let st := satState satMem [⟨0, 34⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 12⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Sample
