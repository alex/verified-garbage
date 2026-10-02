import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Proof.Argon2.X86_64.ReducePointersCT
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockCT

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceLane

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .rbx = BitVec.ofNat 64 lane
  rightLane : t.gpr .rbx = BitVec.ofNat 64 lane
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReducePointers.code
      (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := Related p lane) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .rbp) 232) 64 = t.mem.readW (off (t.gpr .rbp) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReduceLane.code (fun _ _ => True) :=
  (pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.X86_64.ReduceLane
