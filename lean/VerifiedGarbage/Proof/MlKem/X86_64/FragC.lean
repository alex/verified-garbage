import VerifiedGarbage.Proof.MlKem.X86_64.FragS
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM on x86-64: the input of `PRF`, and sequences in a layout

In a layout: the input of `PRF₂(σ, N)` (`prf_pieces`, for `Prfs.lean`), and
two pieces of code in sequence, for constant time (`RelCT.seqL`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (h : keepB bs ws p l = true) (hs : ∀ w ∈ ws', w ∈ ws) : keepB bs ws' p l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw => h.2 w (hs w hw)⟩

/-! ## `PRF₂(σ, N)` -/

theorem shake31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The bytes absorbed: `σ ‖ N`. -/
theorem prf_pieces {s : State} {N : Nat} (hN : bytesAt s.mem (pa s (sc oNB)) 1 = [BitVec.ofNat 8 N]) :
    pieces s [(sigP, 32), (sc oNB, 1)] = bytesAt s.mem (pa s sigP) 32 ++ [BitVec.ofNat 8 N] := by
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hN]

/-! ## Sequences, for constant time -/

/-- Two pieces of code in sequence, from two runs in a layout that satisfy
`I` (what the first piece needs), each piece leaving the layout. -/
theorem RelCT.seqL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c₁ c₂ : Prog isa}
    {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay rbs wbs x → I x → WP isa c₁ x fun x' => (∃ W, PostB x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => LRel rbs wbs x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, PostB x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.1 h.2.1, w₁ y h.1.2.1 h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩) h₂

end VG.Proof.MlKem.X86_64
