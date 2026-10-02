import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqBlock

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF byteOf)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def F (σ : State) (k j : Nat) : Byte := (Spec.MlDsa.G (B σ k) 1008).getD j 0

theorem F_block (σ : State) (k : Nat) {n j : Nat} (hn : n < 6) (hj : j < 168) :
    F σ k (168*n+j) = byteOf (iterF (n+1) (A0 σ k)) j := by
  unfold F
  change (Spec.MlKem.xof (B σ k) 1008).getD (168*n+j) 0 = _
  rw [Proof.MlKem.xof_getD (B σ k) (by omega),Proof.Sha3.Seed34.xofByte_A0 (B_length σ k) hj]

structure Phase (σ : State) (n phase : Nat) (s : State) : Prop where
  env : Env σ s
  x22 : s.gpr .x22 = stateP σ 0
  x23 : s.gpr .x23 = stateP σ 1
  ptrs : ∀ k < 4,s.gpr (bReg k) = bufAt σ k n
  count : (s.gpr .x28).toNat = 6-n
  states : ∀ p < 2,PairAt s.mem (stateP σ p)
    (iterF (n+if p < phase then 1 else 0) (A0 σ (2*p)))
    (iterF (n+if p < phase then 1 else 0) (A0 σ (2*p+1)))
  out : ∀ k < 4,∀ j < 168*(n+if k < 2*phase then 1 else 0),
    s.mem (bufP σ k+BitVec.ofNat 64 j) = F σ k j

theorem phase_state_ptr {σ s : State} {n ph : Nat} (h : Phase σ n ph s) {p : Nat} (hp : p < 2) :
    s.gpr (pReg p) = stateP σ p := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
  · exact h.x22
  · exact h.x23

theorem buf_byte_address (σ : State) (k n j : Nat) (hj : 168*n ≤ j) :
    bufP σ k+BitVec.ofNat 64 j = bufAt σ k n+BitVec.ofNat 64 (j-168*n) := by
  unfold bufP bufAt at'
  rw [Offset.add_add,Offset.add_add]
  exact congrArg (fun a => scr σ+BitVec.ofNat 64 a) (by omega)

/-- A pair's rate writes preserve all preceding bytes and every other stream. -/
theorem old_byte {σ : State} {p n k j : Nat} (hp : p < 2) (hn : n < 6) (hk : k < 4) (hj : j < 1008)
    (ho : j < 168*n ∨ (k ≠ 2*p ∧ k ≠ 2*p+1)) {m m' : Mem}
    (hf : Frame [pairR (stateP σ p),outR (bufAt σ (2*p) n),outR (bufAt σ (2*p+1) n)] m m') :
    m' (bufP σ k+BitVec.ofNat 64 j) = m (bufP σ k+BitVec.ofNat 64 j) := by
  have haddr : bufP σ k+BitVec.ofNat 64 j = at' σ (oBuf+1008*k+j) := by
    unfold bufP at'; rw [Offset.add_add]
  rw [haddr]
  refine hf _ (fun r hr => ?_)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Offset.disjoint (scr σ) (d := oBuf+1008*k+j) (n := 1) (e := 400*p) (k := 400)
      (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega) (by omega)) _ (Region.contains_self _ _)
  · exact (Offset.disjoint (scr σ) (d := oBuf+1008*k+j) (n := 1) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by rcases ho with h | ⟨h,_⟩ <;> omega) (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
      _ (Region.contains_self _ _)
  · exact (Offset.disjoint (scr σ) (d := oBuf+1008*k+j) (n := 1) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by rcases ho with h | ⟨_,h⟩ <;> omega) (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
      _ (Region.contains_self _ _)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
