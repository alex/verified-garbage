import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA on x86 (32-bit): calls of the polynomial primitives

For each signature of the primitives key generation and verification call, a
call (`callP_piece`) of any code verified against its contract (`Callee`),
with its arguments named as buffers and immediates: its precondition on entry
and its public data, from the layout, and its postcondition restated on the
caller's memory.

The facts about regions and the stack of the callee's precondition are
those `Ent.buf` gives for each buffer, `Ent.self` for the callee's own
regions, and `Buf.disj` for pairs of buffers.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs callP callPR)
open VG.Spec.MlDsa (Poly Reduced PolyIs polyAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- Closes the facts of a callee's precondition about its stack and regions,
from those in the context. -/
macro "ent_pre" : tactic => `(tactic| (and_intros <;>
  first | exact True.intro | with_reducible assumption | omega | rfl))

theorem sw_app (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := BitVec.setWidth_append_eq_right

theorem ent_polyAt {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) {a o : Nat}
    (hb : Y.ok ⟨a, o, 1024⟩ = true) :
    polyAt e.mem (Buf.addr s₀ ⟨a, o, 1024⟩) = polyAt s.mem (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.polyAt_congr (he.mem _ hb)

theorem ent_reduced {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) {a o : Nat}
    (hb : Y.ok ⟨a, o, 1024⟩ = true) (h : Reduced s.mem (Buf.addr s₀ ⟨a, o, 1024⟩)) :
    Reduced e.mem (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.reduced_congr (he.mem _ hb) h

/-! ## In place: `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

theorem inPlace_piece {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hc : Callee c fun stk => Spec.MlDsa.inPlaceContract X86.abi t stk) (fa fo wa wo : Nat)
    (hk : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨wa, wo, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨wa, wo, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .buf ⟨wa, wo, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨fa, fo, 1024⟩, ⟨wa, wo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callP Y.sc nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨wa, wo, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hW⟩, dFW⟩ := hk
  have hF' := (Lay.okW_iff.mp hF).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine callP_piece _ [] [⟨fa, fo, 1024⟩, ⟨wa, wo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF', hW']) hN (by simp) (by simp [hF, hW]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF' hK
    obtain ⟨w₁, w₂, w₃, w₄⟩ := he.buf hp hN (by simp) hW' hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF' hW' dFW
    have r₁ := ent_reduced he hF' (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero, List.getElem_cons_succ,
      Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    exact ⟨by omega, by omega, rfl, d₁, f₁, w₁, f₂, w₂, x₁, f₃, w₃, x₂, f₄, w₄, r₁⟩
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF', hW']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, List.getElem_cons_zero, Arg.val, m₂] at post
    rw [ent_polyAt he hF'] at post
    exact hQ s₀ s s' hp ha h' fr post

theorem toNat_ofNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## `vg_mldsa_rej_ntt_poly` -/

theorem rejNtt_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejNTTContract X86.abi stk)
    (da dO aa ao wa wo : Nat)
    (hk : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => Spec.MlDsa.rejNTTPoly b.rejNTT
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_rej_ntt_poly" c [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  refine callPR_piece _ [⟨da, dO, 34⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁]) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
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
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁]) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [List.getElem_cons_zero, Arg.val] at a₀ a₀'
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    exact ⟨esp, by rw [hs], ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂, sw_app] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2


/-! ## Three polynomials: `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`, `vg_mldsa_power2round` -/

section
variable (ha hao fa fo ga go : Nat)

/-- The checks of the buffers of a call with the arguments `h` (written), `f` and `g`. -/
abbrev chk3 (Y : Lay) (h f g : Buf) : Bool :=
  Y.okW h && Y.ok f && Y.ok g && Y.sep h f && Y.sep h g

theorem chk3_iff {h f g : Buf} (hk : chk3 Y h f g = true) :
    Y.okW h = true ∧ Y.ok h = true ∧ Y.ok f = true ∧ Y.ok g = true ∧ Y.sep h f = true ∧ Y.sep h g = true := by
  simp only [chk3, Bool.and_eq_true] at hk
  exact ⟨hk.1.1.1.1, (Lay.okW_iff.mp hk.1.1.1.1).1, hk.1.1.1.2, hk.1.1.2, hk.1.2, hk.2⟩

theorem mul_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulContract X86.abi stk)
    (hk : chk3 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, hao, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) (Spec.MlDsa.multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_multiply_ntt" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  obtain ⟨hHw, hH, hF, hG, dHF, dHG⟩ := chk3_iff hk
  refine callP_piece _ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] [⟨ha, hao, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hF, hG]) (by simp [hHw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have rf := ent_reduced he hF (hA s₀ s hp ha).2.1
    have rg := ent_reduced he hG (hA s₀ s hp ha).2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [ent_polyAt he hF, ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' (fr.mono fun r hr => by simp at hr ⊢; grind) post

theorem mulAdd_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulAddContract X86.abi stk)
    (hk : chk3 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨ha, hao, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩) (Spec.MlDsa.add (polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩))
        (Spec.MlDsa.multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_multiply_add_ntt" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  obtain ⟨hHw, hH, hF, hG, dHF, dHG⟩ := chk3_iff hk
  refine callP_piece _ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] [⟨ha, hao, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hF, hG]) (by simp [hHw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have rh := ent_reduced he hH (hA s₀ s hp ha).2.1
    have rf := ent_reduced he hF (hA s₀ s hp ha).2.2.1
    have rg := ent_reduced he hG (hA s₀ s hp ha).2.2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [ent_polyAt he hH, ent_polyAt he hF, ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' (fr.mono fun r hr => by simp at hr ⊢; grind) post

/-- The checks of the buffers of a call with the arguments `t`, `t₁` and `t₀` (both written). -/
abbrev chkP2 (Y : Lay) (t t1 t0 : Buf) : Bool :=
  Y.ok t && Y.okW t1 && Y.okW t0 && Y.sep t t1 && Y.sep t t0 && Y.sep t1 t0

theorem p2r_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.power2RoundContract X86.abi stk)
    (hk : chkP2 Y ⟨ha, hao, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] 80) s.mem s'.mem →
      Spec.MlDsa.NatPolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩)).map fun c => (Spec.MlDsa.power2Round c).1.toNat) →
      PolyIs s'.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ha, hao, 1024⟩)).map fun c => Spec.MlDsa.ofInt (Spec.MlDsa.power2Round c).2) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_power2round" c [.buf ⟨ha, hao, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [chkP2, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hH, hFw⟩, hGw⟩, dHF⟩, dHG⟩, dFG⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  have hG := (Lay.okW_iff.mp hGw).1
  refine callP_piece _ [⟨ha, hao, 1024⟩] [⟨fa, fo, 1024⟩, ⟨ga, go, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hH, hF, hG]) hN (by simp [hH]) (by simp [hFw, hGw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := he.buf hp hN (by simp) hH hK
    obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hH hF dHF
    have d₂ := Buf.disj hp hH hG dHG
    have d₃ := Buf.disj hp hF hG dFG
    have rh := ent_reduced he hH (hA s₀ s hp ha).2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hH, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [ent_polyAt he hH] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

end

/-! ## Two polynomials: `vg_mldsa_add`, `vg_mldsa_sub` -/

theorem acc_piece {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hc : Callee c fun stk => Spec.MlDsa.accSig.contract X86.abi
      (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := stk))
    (fa fo ga go : Nat)
    (hk : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callP Y.sc nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hFw, hG⟩, dFG⟩ := hk
  have hF := (Lay.okW_iff.mp hFw).1
  refine callP_piece _ [⟨ga, go, 1024⟩] [⟨fa, fo, 1024⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hG]) hN (by simp [hG]) (by simp [hFw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨g₁, g₂, g₃, g₄⟩ := he.buf hp hN (by simp) hG hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hG dFG
    have rf := ent_reduced he hF (hA s₀ s hp ha).2.1
    have rg := ent_reduced he hG (hA s₀ s hp ha).2.2
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hG]) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂] at post
    rw [ent_polyAt he hF, ent_polyAt he hG] at post
    exact hQ s₀ s s' hp ha h' fr post


/-! ## `vg_mldsa_rej_bounded_poly` -/

theorem rejBounded_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejBoundedContract X86.abi stk)
    (da dO η aa ao wa wo : Nat) (hη : η = 2 ∨ η = 4)
    (hk : (Y.ok ⟨da, dO, 66⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨wa, wo, 2048⟩ && Y.sep ⟨da, dO, 66⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 66⟩ ⟨wa, wo, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨wa, wo, 2048⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨da, dO, 66⟩, .imm η, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.MlDsa.rejBoundedLeak η (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66) =
        Spec.MlDsa.rejBoundedLeak η (Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 66⟩) 66))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] 80) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.rejBoundedPoly η b.rejBounded
        (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66)).map Spec.MlDsa.toRq) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callPR Y.sc "vg_mldsa_rej_bounded_poly" c
        [.buf ⟨da, dO, 66⟩, .imm η, .buf ⟨aa, ao, 1024⟩, .buf ⟨wa, wo, 2048⟩]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hD, hAw⟩, hW⟩, dDA⟩, dDW⟩, dAW⟩ := hk
  have hA₁ := (Lay.okW_iff.mp hAw).1
  have hW₁ := (Lay.okW_iff.mp hW).1
  have hη' : η < 2 ^ 32 := by omega
  have eη : (BitVec.ofNat 32 η).toNat = η := toNat_ofNat32 hη'
  refine callPR_piece _ [⟨da, dO, 66⟩] [⟨aa, ao, 1024⟩, ⟨wa, wo, 2048⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hD, hA₁, hW₁, hη']) hN (by simp [hD]) (by simp [hAw, hW]) tt hA
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
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eη] at *
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hD, hA₁, hW₁, hη']) he he'
    have hs := hseed s₀ s₀' s s' hp hp' hq ha ha'
    have a₀ := he.arg 0 (by simp)
    have a₀' := he'.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    rw [← Proof.MlKem.bytesAt_congr (he.mem _ hD), ← Proof.MlKem.bytesAt_congr (he'.mem _ hD)] at hs
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Arg.val] at a₀ a₀' a₁
    simp only [Buf.addr, ← a₀, ← a₀'] at hs
    simp only [arg_withRegions]
    refine ⟨esp, ?_, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
    rw [← ags 1 (by simp), a₁, eη, hs]
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, g₂, sw_app,
      eη] at post
    rw [Proof.MlKem.bytesAt_congr (he.mem _ hD)] at post
    exact hQ s₀ s s' hp ha h' fr post.1 post.2

/-! ## Packing: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

theorem sbp_bounds : ∀ b ∈ Spec.MlDsa.simpleBitPackBounds, b < 2 ^ 32 ∧ 32 * Spec.MlDsa.bitlen b < 2 ^ 32 := by
  decide

theorem sbp_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86.abi stk)
    (fa fo b oa oo L : Nat) (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) (hL : L = 32 * Spec.MlDsa.bitlen b)
    (hk : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, L⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, L⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, L⟩, .imm L])) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧
      ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, L⟩] 80) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, L⟩) L =
        Spec.MlDsa.simpleBitPack (Spec.MlDsa.natPolyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) b → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_simple_bit_pack" c [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, L⟩, .imm L]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hOw⟩, dFO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  obtain ⟨hb', hL'⟩ := sbp_bounds b hb
  rw [← hL] at hL'
  have eb : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 hb'
  have eL : (BitVec.ofNat 32 L).toNat = L := toNat_ofNat32 hL'
  refine callP_piece _ [⟨fa, fo, 1024⟩] [⟨oa, oo, L⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hO, hb', hL']) hN (by simp [hF]) (by simp [hOw]) tt (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hO dFO
    have cb : ∀ i < Spec.MlDsa.n, (Spec.MlDsa.coeffAt e.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b :=
      fun i hi => by rw [Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hF) hi]; exact (hA s₀ s hp ha).2 i hi
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, eb, eL] at *
    have := hb
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hO, hb', hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂, eb,
      eL] at post
    rw [Proof.MlDsa.KeyGen.natPolyAt_congr (he.mem _ hF)] at post
    exact hQ s₀ s s' hp ha h' fr post


theorem bp_bounds : ∀ ab ∈ Spec.MlDsa.bitPackParams, ab.1 < 2 ^ 32 ∧ ab.2 < 2 ^ 32 ∧
    32 * Spec.MlDsa.bitlen (ab.1 + ab.2) < 2 ^ 32 := by
  decide

theorem bp_piece {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.bitPackContract X86.abi stk)
    (fa fo a b oa oo L : Nat) (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hL : L = 32 * Spec.MlDsa.bitlen (a + b))
    (hk : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, L⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, L⟩) = true)
    (hN : 96 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (setArgs Y.sc argRegs [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, L⟩, .imm L])) ht).isSome
      = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      ∀ i < Spec.MlDsa.n, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat
        Spec.MlDsa.q ∧
        Spec.MlDsa.modPm (Spec.MlDsa.coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ≤ b)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ [⟨oa, oo, L⟩] 80) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, L⟩) L =
        Spec.MlDsa.bitPack ((polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q)
          a b → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callP Y.sc "vg_mldsa_bit_pack" c [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, L⟩, .imm L]) := by
  obtain ⟨⟨K, hK, hv⟩, hst, hsp⟩ := hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hF, hOw⟩, dFO⟩ := hk
  have hO := (Lay.okW_iff.mp hOw).1
  obtain ⟨hav, hbv, hL'⟩ := bp_bounds (a, b) hab
  rw [← hL] at hL'
  have ea : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 hav
  have eb : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 hbv
  have eL : (BitVec.ofNat 32 L).toNat = L := toNat_ofNat32 hL'
  refine callP_piece _ [⟨fa, fo, 1024⟩] [⟨oa, oo, L⟩] hv hsp hst (by simp) (by simp)
    (by simp [Arg.ok, hF, hO, hav, hbv, hL']) hN (by simp [hF]) (by simp [hOw]) tt
    (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, post⟩ => ?_)
  · obtain ⟨f₁, f₂, f₃, f₄⟩ := he.buf hp hN (by simp) hF hK
    obtain ⟨o₁, o₂, o₃, o₄⟩ := he.buf hp hN (by simp) hO hK
    obtain ⟨x₁, x₂⟩ := he.self hp hN (by simp) hK
    obtain ⟨en, hE⟩ := he.espNat hp hN (by simp)
    have d₁ := Buf.disj hp hF hO dFO
    have rf := ent_reduced he hF (hA s₀ s hp ha).2.1
    have cb : ∀ i < Spec.MlDsa.n, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt e.mem
        (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ∧
        Spec.MlDsa.modPm (Spec.MlDsa.coeffAt e.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat Spec.MlDsa.q ≤ b :=
      fun i hi => by rw [Proof.MlDsa.KeyGen.coeffAt_congr (he.mem _ hF) hi]; exact (hA s₀ s hp ha).2.2 i hi
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, List.getElem_cons_zero,
      List.getElem_cons_succ, Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, ea, eb,
      eL] at *
    have := hab
    have := hL
    ent_pre
  · obtain ⟨esp, ags⟩ := call_pubs _ hq (by simp [Arg.ok, hF, hO, hav, hbv, hL']) he he'
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    simp only [arg_withRegions]
    exact ⟨esp, ags 0 (by simp), ags 1 (by simp), ags 2 (by simp), ags 3 (by simp), ags 4 (by simp)⟩
  · have a₀ := he.arg 0 (by simp)
    have a₁ := he.arg 1 (by simp)
    have a₂ := he.arg 2 (by simp)
    have a₃ := he.arg 3 (by simp)
    have a₄ := he.arg 4 (by simp)
    generalize e = e' at *
    sig_post [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, a₄, List.getElem_cons_zero, List.getElem_cons_succ, Arg.val, m₂,
      ea, eb, eL] at post
    rw [ent_polyAt he hF] at post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlDsa.X86.KeyGen
