import VerifiedGarbage.Proof.Ed25519.Arm.BatchBits
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTBits`. -/
section
/-! Reloading the scalar pointer and batch index restores their public values. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BitsCTPre (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j

theorem batchBits_ct (b p : BitVec 32) (j : Nat) :
    CT (fun x y => BitsCTPre b p j x ∧ BitsCTPre b p j y)
      (.block batchBits) (fun x y => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r) := by
  let head : List Instr := [.ldr .r12 .r0 52, .ldr .r2 .r0 56]
  have hh : CT (fun x y => BitsCTPre b p j x ∧ BitsCTPre b p j y)
      (.block head) (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = p ∧ x.gpr .r2 = BitVec.ofNat 32 j) ∧
        (y.gpr .r0 = b ∧ y.gpr .r12 = p ∧ y.gpr .r2 = BitVec.ofNat 32 j)) := by
    apply ctBoth
    · dsimp only [head]
      apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hp, hj⟩
      refine ldr0_ok hc (by decide) fun u hu =>
        ldr0_ok (hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)) (by decide)
          fun t ht => WP.block_nil ?_
      refine ⟨(ht.other _ (by decide)).trans ((hu.other _ (by decide)).trans hc.r0),
        (ht.other _ (by decide)).trans (hu.gpr.trans hp), ?_⟩
      rw [ht.gpr, hu.mem]
      exact hj
  change CT _ (.block (head ++
    (([.dp .add .r12 .r12 (.shifted .r2 .lsl 1)] : List Instr) ++ unpackSrc 0 0 ++ expandBits))) _
  refine ctBlockAppend hh ?_
  dsimp only [head]
  apply ctRegsKeeping [.r0, .r12, .r2] [.r0] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.1.trans h.2.2.1.symm
  · exact h.1.2.2.trans h.2.2.2.symm

end VG.Proof.Ed25519.Arm
end

/-! Each batch uses the same public checkpoint and scalar-byte addresses. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BodyCTPre (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1) ∧
    env s.mem b 16 = Spec.Ed25519.d

def BodyCTReady (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j ∧
    env s.mem b 16 = Spec.Ed25519.d ∧ s.gpr .r11 = BitVec.ofNat 32 j

theorem batchStart_ct (b p : BitVec 32) (j : Nat) :
    CT (fun x y => BodyCTPre b p j x ∧ BodyCTPre b p j y)
      (.block batchStart) (fun x y => BodyCTReady b p j x ∧ BodyCTReady b p j y) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.r0.trans h.2.1.r0.symm
  · intro s ⟨hc, hl, hi, hj, hd⟩
    refine WP.mono (batchStart_ok hc j hj) fun t ⟨tr, tf, tv, tc⟩ => ?_
    have tk : MulKeep b 5696 2048 s t := MulKeep.of_counter tr (by decide) tf
    exact ⟨tk.ctx hc, smallFrame_lim tf (by decide) hl, (tk.word (by decide) (by decide) 52 (.inr rfl)).trans hi, tc,
      (congrFun (smallFrame_env tf (by decide)) 16).trans hd, tv⟩

theorem prepareBatch_ct (b p : BitVec 32) (j : Nat) (hj : j < 32) :
    CT (fun x y => BodyCTReady b p j x ∧ BodyCTReady b p j y)
      prepareBatch (fun x y => BitsCTPre b p j x ∧ BitsCTPre b p j y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r11] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm
  · intro s ⟨hc, hl, hi, hcj, hd, hv⟩
    refine WP.mono (prepareBatch_ok hc hl j hj hv hd) fun t ⟨tk, _, _, _, _⟩ => ?_
    exact ⟨tk.ctx hc, ((MulKeep.of_powers tk).word (by decide) (by decide) 52 (.inr rfl)).trans hi,
      (tk.counter (by decide) (by decide)).trans hcj⟩

theorem pointMulBody_ct (b p : BitVec 32) (j : Nat) (hj : j < 32) :
    CT (fun x y => BodyCTPre b p j x ∧ BodyCTPre b p j y)
      pointMulBody (fun _ _ => True) := by
  rw [pointMulBody]
  refine RelCT.seq (batchStart_ct b p j)
    (RelCT.seq (prepareBatch_ct b p j hj) (RelCT.seq (batchBits_ct b p j) ?_))
  apply ctRegs [.r0] _ (by taint_decide)
  intro x y h
  exact h

end VG.Proof.Ed25519.Arm
