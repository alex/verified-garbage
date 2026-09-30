import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT

/-!
# ML-DSA signing on ARMv7: copies leak only their addresses

Untrusted: everything here is checked by Lean. The setup of a copy
accesses no memory, and its loop leaks only the pointers and the count in
`r0`–`r2` (by the taint analysis), so two runs of a copy between the same
addresses leak the same (`copy_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign

theorem copySetup_nomem (dst src : Ptr) (n : Nat) :
    ∀ i ∈ lea .r0 src ++ lea .r1 dst ++ movi .r2 n, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ bases) (b2 : dst.1 ∈ bases) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  unfold copy
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ [Reg.r0, .r1, .r2], x.gpr r = y.gpr r)
    (postDep (block_nomem_tr (copySetup_nomem dst src n))
      (fun x y _ => ⟨copySetup_ok b1 b2 x, copySetup_ok b1 b2 y⟩)
      fun x y x' y' hp ⟨a0, a1, a2, _⟩ ⟨c0, c1, c2, _⟩ => ?_)
    (VG.Proof.MlKem.Arm.taint_prog [.r0, .r1, .r2] (fun _ _ h => h) (by taint_decide))
  obtain ⟨e1, e2⟩ := hP x y hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, c0, e2]
  · rw [a1, c1, e1]
  · rw [a2, c2]

end VG.Proof.MlDsa.Arm.Sign
