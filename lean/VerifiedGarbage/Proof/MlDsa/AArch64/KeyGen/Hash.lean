import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-DSA on AArch64: `H`, SHAKE256

`shake256 ins [out]` (ML-KEM's `hash` on AArch64,
`Proof/MlKem/AArch64/HashProof.lean`, with the Keccak state and its working
space at the start of `scratch`): if the pieces are in the layout (a check
evaluated on the pointers, `hashChk`), it writes `H` of the concatenation of
the input pieces to the output piece, and changes nothing else but the Keccak
state and working space and the 16 bytes of stack below the stack pointer
(`shake_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (HSetup PieceOk preg pbytes Kept Outs hashWith_ok)
open VG.Spec.Sha3 (bytesAt)

/-- The pointer and length of a piece. -/
abbrev pieceP (q : Impl.MlKem.AArch64.Piece) : Ptr × Nat := ((q.base, q.off), q.len)

/-- A piece in the layout (written if `w`), apart from the Keccak state and working space. -/
def pieceChk (rbs wbs : List (Reg × Nat)) (w : Bool) (q : Impl.MlKem.AArch64.Piece) : Bool :=
  decide (q.off < 65536) && decide (q.len < 65536) &&
    (if w then inB wbs (q.base, q.off) q.len else true) &&
    sepB rbs wbs (q.base, q.off) q.len (sc 0) 200 && sepB rbs wbs (q.base, q.off) q.len (sc 200) 640

/-- `shake256 ins [out]` can run in the layout. -/
def hashChk (rbs wbs : List (Reg × Nat)) (ins : List Impl.MlKem.AArch64.Piece) (out : Impl.MlKem.AArch64.Piece) :
    Bool :=
  inB wbs (sc 0) 200 && inB wbs (sc 200) 640 && sepB rbs wbs (sc 0) 200 (sc 200) 640 &&
    ins.all (pieceChk rbs wbs false) && pieceChk rbs wbs true out

theorem hashChk_parts {rbs wbs : List (Reg × Nat)} {ins : List Impl.MlKem.AArch64.Piece}
    {out : Impl.MlKem.AArch64.Piece} (hc : hashChk rbs wbs ins out = true) :
    inB wbs (sc 0) 200 = true ∧ inB wbs (sc 200) 640 = true ∧ sepB rbs wbs (sc 0) 200 (sc 200) 640 = true ∧
      (∀ q ∈ ins, pieceChk rbs wbs false q = true) ∧ pieceChk rbs wbs true out = true := by
  simp only [hashChk, Bool.and_eq_true, List.all_eq_true] at hc
  exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) (h16 : 16 ≤ S) (hS : S < 2 ^ 64)
include L h16 hS

theorem Lay.stk16 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨pa s p, l⟩ :=
  (L.stkD h).sub_left (below_sub h16 hS)

theorem hsetup (hc : inB wbs (sc 0) 200 = true) (hc' : inB wbs (sc 200) 640 = true)
    (hd : sepB rbs wbs (sc 0) 200 (sc 200) 640 = true) : HSetup .x28 0 200 136 s := by
  have i1 : inB (rbs ++ wbs) (sc 0) 200 = true := (sepB_spec hd).1
  have i2 : inB (rbs ++ wbs) (sc 200) 640 = true := (sepB_spec hd).2.1
  have hd' := L.disj hd
  have k1 := L.stk16 h16 hS i1
  have k2 := L.stk16 h16 hS i2
  have cv := Covers.cons (L.cW hc) (L.cW hc')
  simp only [pa] at hd' k1 k2 cv
  have hr : (136 : Nat) ∈ Spec.Sha3.rates := by simp [Spec.Sha3.rates]
  have hsp : 16 ≤ s.sp.toNat := by have := L.spS; omega
  exact ⟨by decide, by decide, by decide, hr, hd', hsp, k1, k2, cv⟩

theorem pieceOk {w : Bool} {q : Impl.MlKem.AArch64.Piece} (hc : pieceChk rbs wbs w q = true) :
    PieceOk .x28 0 200 s w q := by
  simp only [pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hl⟩, hw⟩, d1⟩, d2⟩ := hc
  have hin : inB (rbs ++ wbs) (q.base, q.off) q.len = true := (sepB_spec d1).1
  have hb : q.base ∈ bases := L.ptrBs hin
  have e1 := L.disj d1
  have e2 := L.disj d2
  have e3 := L.stk16 h16 hS hin
  simp only [pa] at e1 e2 e3
  refine ⟨bases_pres _ hb, ho, hl, e1, e2, e3, ?_⟩
  cases w
  · exact L.cR hin
  · simp only [ite_true] at hw ⊢; exact L.cW hw

end

theorem shake256_eq' (m : List Byte) (d : Nat) :
    Spec.MlDsa.H m d = Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 0x1f) m)) 0 d :=
  Proof.MlKem.shake256_eq m d

/-- `H` of the input pieces, to the output piece. -/
theorem shake_ok {S : Nat} (h16 : 16 ≤ S) (hS : S < 2 ^ 64) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {ins : List Impl.MlKem.AArch64.Piece} {out : Impl.MlKem.AArch64.Piece}
    (hne : ins ≠ []) (hc : hashChk rbs wbs ins out = true) :
    WP isa ((shake256With keccak.callee) ins [out]) s fun s' =>
      PPostB S s s' [(sc 0, 200), (sc 200, 640), pieceP out] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s (out.base, out.off)) out.len = Spec.MlDsa.H (ins.map (pbytes s)).flatten out.len := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hashChk_parts hc
  refine WP.mono (hashWith_ok keccak (hsetup L h16 hS c1 c2 c3) (by decide) hne (fun q hq => pieceOk L h16 hS (c4 q hq))
    (fun q hq => by rw [List.mem_singleton.mp hq]; exact pieceOk L h16 hS c5) (List.pairwise_singleton _ _))
    fun s' ⟨k', o'⟩ => ⟨⟨k'.rd, k'.wr, k'.sp, fun r hr => k'.cs r (kept_pres r hr).1 (kept_pres r hr).2, ?_, k'.vcs⟩,
      k'.cs .x24 (by decide) (by decide), ?_⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub h16 hS⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),
        fun _ h => h⟩
  · rw [shake256_eq']
    exact o'.1

end VG.Proof.MlDsa.AArch64.KeyGen
