import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddArgs
import VerifiedGarbage.Spec.Ed25519.Contract

/-! A local contract for the five-argument scalar multiply-add ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarMulAddLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let r : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let k : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let a : Region := ⟨State.addr (s.gpr .r3), 32⟩
    let ws : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, ws] ∧
      out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws ∧
      out.Disjoint args ∧ ws.Disjoint args ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0

structure ScalarMulAddPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (s.gpr .r2), 32⟩,
    ⟨State.addr (s.gpr .r3), 32⟩, ⟨State.addr s.sp, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (stackArg s 0), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  r_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  k_ws : (⟨State.addr (s.gpr .r2), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  a_ws : (⟨State.addr (s.gpr .r3), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  out_args : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  ws_args : (⟨State.addr (stackArg s 0), 8192⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 32 ≤ 2 ^ 32
  fs : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  fsp : s.sp.toNat + 4 ≤ 2 ^ 32

theorem ScalarMulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : ScalarMulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ScalarMulAddPre.input {s : State} (h : ScalarMulAddPre s) {i : Nat} (hi : i < 3) :
    (s.gpr (scalarArgReg (i + 1))).toNat + 32 ≤ 2 ^ 32 ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩ := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [scalarArgReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [scalarArgReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [scalarArgReg], h.a_ws⟩

end VG.Proof.Ed25519.Arm
