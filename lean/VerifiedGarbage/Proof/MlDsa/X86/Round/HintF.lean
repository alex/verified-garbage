import VerifiedGarbage.Proof.MlDsa.X86.Round.Hint

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_make_hint` and `vg_mldsa_use_hint`

Untrusted: everything here is checked by Lean. Both functions are the
prologue and the loops of `Hint.lean`; `makeHint` then returns the count in
`ecx`, which is the number of 1s (`sumV_ones`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced polyAt HintIs NatPolyIs hintOnes hintAt makeHintContract
  makeHintSig useHintContract useHintSig)
open VG.Proof.MlDsa.Round (coeffAddr pR n_eq q_eq polyAt_val hintIs_of_toNat natPolyIs_of_toNat zipWith_get
  hintAt_get onesFrom onesFrom_step onesFrom_n hintOnes_single makeHint_eq useHint_eq)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState toNat_ofNat32
  setWidth_append32)

theorem HPre.of_mh {s₀ : State} (h : (makeHintContract X86.abi 16).pre s₀) : HPre true s₀ := by
  sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun _ => h22, h23⟩

theorem HPre.of_uh {s₀ : State} (h : (useHintContract X86.abi 16).pre s₀) : HPre false s₀ := by
  sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    fun h => absurd h (by decide), h22⟩

/-! ## `useHint` -/

theorem uh_piece : Piece (HPre false) HPub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => HInv (uhV (arg s₀ 2).toNat) false s₀ 256 s) s₀ s') useHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (hintInit_piece false) (hint_ite (fun g hg => uhCore_spec hg) (by taint_decide)
      (by taint_decide))).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem uhV_lt {g : Nat} (hg : g ∈ gamma2s) (a b : Nat) : uhV g a b < 2 ^ 32 := by
  have hm : 0 < VG.Proof.MlDsa.Round.hbM g := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  have : VG.Proof.MlDsa.Round.hbM g ≤ 44 := by
    rcases VG.Proof.MlDsa.Round.mem_gamma2s hg with e | e <;> rw [e] <;> decide
  unfold uhV
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) (by omega)

theorem uh_post {s₀ s : State} (hp : HPre false s₀) (h : HInv (uhV (arg s₀ 2).toNat) false s₀ 256 s) :
    NatPolyIs s.mem (pA s₀ 3) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint (arg s₀ 2).toNat hj rj).toNat)
      ((hintAt s₀.mem (pA s₀ 0) 1).headD (Vector.replicate VG.Spec.MlDsa.n false)) (polyAt s₀.mem (pA s₀ 1))) := by
  refine natPolyIs_of_toNat fun i hi => ?_
  rw [h.out i hi, zipWith_get _ _ _ hi, hintAt_get _ _ hi, useHint_eq hp.g2, polyAt_val hp.b_red hi,
    toNat_ofNat32 (uhV_lt hp.g2 _ _), Int.toNat_natCast]
  unfold uhV
  congr 1
  by_cases e : coeffAt s₀.mem (pA s₀ 0) i = 0
  · have e' : cA s₀ i = 0 := by simp [cA, e]
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = false := decide_eq_false fun h => h e
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h' e')]
    simp only [d, Bool.false_eq_true, ↓reduceIte]
  · have e' : cA s₀ i ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    have d : decide (coeffAt s₀.mem (pA s₀ 0) i ≠ 0) = true := decide_eq_true e
    rw [ite_eq_left_of_eq_true _ _ (eq_true e')]
    simp only [d, ↓reduceIte]

/-- Memory with the arguments `0x400`, `0x800`, `(q - 1)/32` and `0` at `0x5004`. -/
def hintSatMem : Mem := fun a =>
  if a = 0x5005 then 4 else if a = 0x5009 then 8 else if a = 0x500d then 0xff else if a = 0x500e then 3 else 0

theorem hintSat_zero (a : Addr) (ha : a.toNat < 0x5000) : hintSatMem a = 0 := by
  simp only [hintSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]

theorem useHint_verified : Verified X86.target useHint (useHintContract X86.abi 16) := by
  refine Piece.verified ((uh_piece.pre_mono (fun _ h => HPre.of_uh h) fun s s' _ _ h => by
      sig_pub [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact uh_post (HPre.of_uh h₀) hinv
  · let st := satState hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [useHintContract, useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `makeHint` -/

/-- After the loops, the count to `eax`. -/
def MhEnd (s₀ s : State) : Prop :=
  HInv (mhV (arg s₀ 2).toNat) true s₀ 256 s ∧ s.gpr .eax = BitVec.ofNat 32 (sumV (mhV (arg s₀ 2).toNat) s₀ 256)

theorem mh_piece : Piece (HPre true) HPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MhEnd s₀) s₀ s')
    makeHint :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 3), aR s₀ 4]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (hintInit_piece true) (Piece.seq (hint_ite (fun g hg => mhCore_spec hg) (by taint_decide)
      (by taint_decide)) (Piece.taint [] (fun s₀ s hp h => wp_mov fun s₁ u₁ => WP.block_nil_iff.mpr
        ⟨⟨by rw [u₁.other _ (by decide), h.esp], by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr],
          by rw [u₁.other _ (by decide), h.esi], by rw [u₁.other _ (by decide), h.edi],
          by rw [u₁.other _ (by decide), h.ebp], by rw [u₁.mem]; exact h.frame, by rw [u₁.mem]; exact h.slot,
          fun i hi => by rw [u₁.mem]; exact h.out i hi, fun e => by rw [u₁.other _ (by decide)]; exact h.ecx e⟩,
          by rw [u₁.gpr]; exact h.ecx rfl⟩)
        (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)

theorem mhV_le {g a b : Nat} : mhV g a b ≤ 1 := by unfold mhV; split <;> omega

theorem sumV_le {g : Nat} {s₀ : State} : ∀ k, sumV (mhV g) s₀ k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by have := sumV_le (g := g) (s₀ := s₀) k; have := @mhV_le g (cA s₀ k) (cB s₀ k); simp only [sumV]; omega

/-- The hint of `makeHint`, coefficient by coefficient. -/
theorem mh_get {s₀ : State} (hp : HPre true s₀) {i : Nat} (hi : i < 256) :
    ((Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1)))[i]!).toNat = mhV (arg s₀ 2).toNat (cA s₀ i) (cB s₀ i) := by
  have hi' : i < VG.Spec.MlDsa.n := by rw [n_eq]; exact hi
  rw [zipWith_get _ _ _ hi', makeHint_eq hp.g2, polyAt_val (hp.a_red rfl) hi', polyAt_val hp.b_red hi', mhV]
  by_cases e : hbV (arg s₀ 2).toNat (cB s₀ i) = hbV (arg s₀ 2).toNat ((cB s₀ i + cA s₀ i) % q)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
    simp only [hbV] at e
    simp [e]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
    simp only [hbV] at e
    simp [e]

theorem sumV_ones {s₀ : State} (hp : HPre true s₀) :
    ∀ k ≤ 256, sumV (mhV (arg s₀ 2).toNat) s₀ k + onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat)
      (polyAt s₀.mem (pA s₀ 0)) (polyAt s₀.mem (pA s₀ 1))) k =
      onesFrom (Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
        (polyAt s₀.mem (pA s₀ 1))) 0
  | 0, _ => Nat.zero_add _
  | k + 1, hk => by
    rw [← sumV_ones hp k (by omega), onesFrom_step _ (show k < VG.Spec.MlDsa.n by rw [n_eq]; omega), mh_get hp (by omega)]
    simp only [sumV]
    omega

theorem mh_post {s₀ s : State} (hp : HPre true s₀) (h : MhEnd s₀ s) :
    HintIs s.mem (pA s₀ 3) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] ∧
    (s.gpr .eax).toNat = hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint (arg s₀ 2).toNat) (polyAt s₀.mem (pA s₀ 0))
      (polyAt s₀.mem (pA s₀ 1))] := by
  refine ⟨hintIs_of_toNat fun j hj => ?_, ?_⟩
  · rw [h.1.out j hj]
    exact congrArg (BitVec.ofNat 32) (mh_get hp hj).symm
  · rw [h.2, toNat_ofNat32 (by have := sumV_le (g := (arg s₀ 2).toNat) (s₀ := s₀) 256; omega), hintOnes_single,
      ← sumV_ones hp 256 (Nat.le_refl _), show (256 : Nat) = VG.Spec.MlDsa.n from rfl, onesFrom_n, Nat.add_zero]

theorem makeHint_verified : Verified X86.target makeHint (makeHintContract X86.abi 16) := by
  refine Piece.verified ((mh_piece.pre_mono (fun _ h => HPre.of_mh h) fun s s' _ _ h => by
      sig_pub [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    have hp := HPre.of_mh h₀
    have ⟨p1, p2⟩ := mh_post hp hinv
    sig_post [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, setWidth_append32, hax]
    exact ⟨p1, p2⟩
  · let st := satState hintSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 0x800 := by decide
    have a2 : arg st 2 = 261888 := by decide
    have a3 : arg st 3 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, reduced_zero hintSat_zero 0x400 (by decide),
      reduced_zero hintSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Round
