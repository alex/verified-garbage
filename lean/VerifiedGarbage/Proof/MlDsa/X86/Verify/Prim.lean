import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2

/-!
# ML-DSA on x86 (32-bit): calls of the primitives verification calls

As `KeyGen/Prim.lean`, for the signatures of `vg_mldsa_sample_in_ball`,
`vg_mldsa_use_hint`, `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`,
`vg_mldsa_hint_bit_unpack` and `vg_mldsa_norm_lt` (which may not write its
arguments: `callPR_pieceRO`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs callP callPR)
open VG.Spec.MlDsa (Poly Reduced PolyIs polyAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## `vg_mldsa_sample_in_ball` -/

theorem ball_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.sampleInBallContract X86.abi stk)
    (da dO L τ aa ao wa wo : Nat) (hb : (L, τ) ∈ Spec.MlDsa.ballParams)
    (hk : (Y.ok ⟨da, dO, L⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, L⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, L⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, L⟩) L)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.sampleInBall τ b.ball
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, L⟩) L)).map Spec.MlDsa.toRq) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_sample_in_ball" c
        [.buf ⟨da, dO, L⟩, .imm L, .imm τ, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  have hbnd : L < 2 ^ 32 ∧ τ < 2 ^ 32 := by
    simp only [Spec.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb; omega
  have eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hbnd.1
  have eτ : (BitVec.ofNat 32 τ).toNat = τ := KeyGen.toNat_ofNat32 hbnd.2
  refine callPR_piece _ [⟨da, dO, L⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨b₁, b₂, b₃, b₄⟩ := he.buf hp hN (by simp) hD hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hA₁ hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW₁ hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hD hA₁ dDA
    have d₂ := Buf.disj hp hD hW₁ dDW
    have d₃ := Buf.disj hp hA₁ hW₁ dAW
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eL, eτ] at *
    have := hb
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁, hbnd]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', eL, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂,
      sw_app, eL, eτ] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

/-! ## `vg_mldsa_use_hint` -/

theorem useHint_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.useHintContract X86.abi stk)
    (ha hao ra ro g oa oo : Nat) (hg : g ∈ Spec.MlDsa.gamma2s)
    (hk : (Y.ok ⟨ha, hao, 1024⟩ && Y.ok ⟨ra, ro, 1024⟩ && Y.okW ⟨oa, oo, 1024⟩ && Y.sep ⟨ha, hao, 1024⟩ ⟨oa, oo, 1024⟩ &&
      Y.sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]))
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      Spec.MlDsa.NatPolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (Vector.zipWith (fun hj rj => (Spec.MlDsa.useHint g hj rj).toNat)
          ((Spec.MlDsa.hintAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) 1).headD (Vector.replicate Spec.MlDsa.n false))
          (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_use_hint" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hH, hR⟩, hOw⟩, dHO⟩, dRO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  have hgb : g < 2 ^ 32 := by
    simp only [Spec.MlDsa.gamma2s, Spec.MlDsa.q, List.mem_cons, List.not_mem_nil, or_false] at hg; omega
  have eg : (BitVec.ofNat 32 g).toNat = g := KeyGen.toNat_ofNat32 hgb
  refine callP_piece _ [⟨ha, hao, 1024⟩, ⟨ra, ro, 1024⟩] [⟨oa, oo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hR, hO, hgb]) hN (by simp [hH, hR]) (by simp [hOw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨r₁, r₂, r₃, r₄⟩ := he.buf hp hN (by simp) hR hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hO dHO
    have d₂ := Buf.disj hp hR hO dRO
    have rr := ent_reduced he hR (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eg] at *
    have := hg
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hR, hO, hgb]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      eg] at post
    rw [ent_polyAt he hR, Proof.MlDsa.Pack.hintAt_congr (fun t ht =>
      Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hH) (by simp only [Spec.MlDsa.n]; omega))] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

theorem bu_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.bitUnpackContract X86.abi stk)
    (va vo L a b fa fo : Nat) (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hL : L = 32 * Spec.MlDsa.bitlen (a + b))
    (hk : (Y.ok ⟨va, vo, L⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, L⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, L⟩) L) a b)) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_bit_unpack" c [.buf ⟨va, vo, L⟩, .imm L, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  obtain ⟨hav, hbv, hL'⟩ := bp_bounds (a, b) hab
  rw [← hL] at hL'
  have ea : (BitVec.ofNat 32 a).toNat = a := KeyGen.toNat_ofNat32 hav
  have eb : (BitVec.ofNat 32 b).toNat = b := KeyGen.toNat_ofNat32 hbv
  have eL : (BitVec.ofNat 32 L).toNat = L := KeyGen.toNat_ofNat32 hL'
  refine callP_piece _ [⟨va, vo, L⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV, hav, hbv, hL']) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hV hF dVF
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, ea, eb,
      eL] at *
    have := hab
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hV, hav, hbv, hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.bitUnpackContract, Spec.MlDsa.bitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, a₄, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      ea, eb, eL] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr post

theorem t1_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.unpackT1Contract X86.abi stk)
    (va vo fa fo : Nat)
    (hk : (Y.ok ⟨va, vo, 320⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨va, vo, 320⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        ((Spec.MlDsa.simpleBitUnpack (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨va, vo, 320⟩) 320) Spec.MlDsa.t1Max).map
          fun c => Spec.MlDsa.ofInt (c * 2 ^ Spec.MlDsa.d : Nat)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_unpack_t1" c [.buf ⟨va, vo, 320⟩, .buf ⟨fa, fo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hV, hFw⟩, dVF⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  refine callP_piece _ [⟨va, vo, 320⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hV]) hN (by simp [hV]) (by simp [hFw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨v₁, v₂, v₃, v₄⟩ := he.buf hp hN (by simp) hV hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hV hF dVF
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hV]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.unpackT1Contract, Spec.MlDsa.unpackT1Sig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hV)] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_hint_bit_unpack` -/

theorem hu_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.hintBitUnpackContract X86.abi stk)
    (ya yo ω k ha ho : Nat) (hwk : (ω, k) ∈ Spec.MlDsa.hintParams)
    (hk : (Y.ok ⟨ya, yo, ω + k⟩ && Y.okW ⟨ha, ho, 256 * k * 4⟩ && Y.sep ⟨ya, yo, ω + k⟩ ⟨ha, ho, 256 * k * 4⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω, .buf ⟨ha, ho, 256 * k * 4⟩,
        .imm (256 * k)])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k) =
        Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨ya, yo, ω + k⟩) (ω + k))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, ho, 256 * k * 4⟩] 80) s.mem s'.mem →
      (match Spec.MlDsa.hintBitUnpack ω k (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ya, yo, ω + k⟩) (ω + k)) with
        | some hint => s'.gpr .eax = 1 ∧ Spec.MlDsa.HintIs s'.mem (Buf.addr s₀ ⟨ha, ho, 256 * k * 4⟩) k hint
        | none => s'.gpr .eax = 0) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_hint_bit_unpack" c [.buf ⟨ya, yo, ω + k⟩, .imm (ω + k), .imm ω,
        .buf ⟨ha, ho, 256 * k * 4⟩, .imm (256 * k)]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hYb, hHw⟩, dYH⟩ := hk
  have hH := (Lay.okW_iff.mp hHw).1
  have hb : ω + k < 2 ^ 32 ∧ ω < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
    simp only [Spec.MlDsa.hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwk; omega
  have e1 : (BitVec.ofNat 32 (ω + k)).toNat = ω + k := KeyGen.toNat_ofNat32 hb.1
  have e2 : (BitVec.ofNat 32 ω).toNat = ω := KeyGen.toNat_ofNat32 hb.2.1
  have e3 : (BitVec.ofNat 32 (256 * k)).toNat = 256 * k := KeyGen.toNat_ofNat32 hb.2.2
  have e4 : ω + k - ω = k := by omega
  refine callPR_piece _ [⟨ya, yo, ω + k⟩] [⟨ha, ho, 256 * k * 4⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hYb, hH, hb]) hN (by simp [hYb]) (by simp [hHw]) tt hA
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨y₁, y₂, y₃, y₄⟩ := he.buf hp hN (by simp) hYb hK
    obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hYb hH dYH
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, e1, e2, e3,
      e4] at *
    have := hwk
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hYb, hH, hb]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₁' := he'.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hYb), ← Proof.MlKem.bytesAt_congr (he'.mem _ hYb)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁ a₁'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
    rw [a₁, a₁', e1, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.hintBitUnpackContract, Spec.MlDsa.hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂,
      sw_app, e1, e2, e4] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hYb)] at post
    exact hQ s₀ s s' hp ha h' fr post

/-! ## `vg_mldsa_norm_lt` -/

theorem normLt_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.normLtContract X86.abi stk)
    (fa fo bd : Nat) (hbd : bd < 2 ^ 32) (hk : Y.ok ⟨fa, fo, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm bd])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [] 80) s.mem s'.mem →
      s'.gpr .eax = (if Spec.MlDsa.normRq [polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)] < bd then 1 else 0) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callPR Y.sc "vg_mldsa_norm_lt" c [.buf ⟨fa, fo, 1024⟩, .imm bd]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  have eb : (BitVec.ofNat 32 bd).toNat = bd := KeyGen.toNat_ofNat32 hbd
  refine callPR_pieceRO _ [⟨fa, fo, 1024⟩] [] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hk, hbd]) hN (by simp [hk]) (by simp) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hk hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have rf := ent_reduced he hk (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eb] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hk, hbd]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, g₂, sw_app,
      eb] at post
    rw [ent_polyAt he hk] at post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlDsa.X86.Verify
