import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Control
open VG.Proof.Sha3.AArch64
open VG.Proof.Sha3.AArch64.Scalar.Boundary

/-- The pointer comparison is a finite fact about public offsets; the caller's
possibly wrapping scratch address cancels before this check. -/
theorem const_offset_test : ∀ k ≤ 24,
    (BitVec.ofNat 64 (128 + 8*k) - BitVec.ofNat 64 320 != 0) = decide (k < 24) := by
  decide +kernel

theorem constAddr_test (orig : State) (k : Nat) (hk : k ≤ 24) :
    (constAddr orig k - constAddr orig 24 != 0) = decide (k < 24) := by
  simp only [constAddr,Offset.add_sub_add_left]
  exact const_offset_test k hk

@[irreducible] def prefixState (A : Spec.Sha3.State) (k : Nat) : Spec.Sha3.State :=
  (List.range k).foldl Spec.Sha3.rnd A

theorem prefixState_zero (A : Spec.Sha3.State) : prefixState A 0 = A := by
  unfold prefixState
  rfl

theorem prefixState_succ (A : Spec.Sha3.State) (k : Nat) :
    prefixState A (k + 1) = Spec.Sha3.rnd (prefixState A k) k := by
  simp only [prefixState,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem prefixState_final (A : Spec.Sha3.State) : prefixState A 24 = Spec.Sha3.keccakF A := by
  unfold prefixState Spec.Sha3.keccakF
  rfl

def LoopInv (orig : State) (A : Spec.Sha3.State) (k : Nat) (s : State) : Prop :=
  Ready orig (prefixState A k) k s ∧
    (0 < k → s.gpr .x27 = constAddr orig k - constAddr orig 24)

/-- The core is invoked through its semantic stage contract. Constant memory
and public vector pointers persist through every round of the counted loop. -/
theorem middle_ok (core : List Instr)
    (hcore : ∀ orig A k s, VG.Proof.Sha3.AArch64.Pre orig → Ready orig A k s →
      WP isa (.block core) s (Ready orig (Spec.Sha3.chi (Spec.Sha3.pi
        (Spec.Sha3.rho (Spec.Sha3.theta A)))) k))
    (orig : State) (A : Spec.Sha3.State) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : CoreState orig A s) :
    WP isa (middle core) s (CoreState orig (Spec.Sha3.keccakF A)) := by
  unfold middle
  rw [WP.seq_iff]
  refine (setup_ok orig A s hp hs).mono fun q hq => ?_
  have hi : LoopInv orig A 0 q := by
    refine ⟨?_,fun h => by omega⟩
    simpa only [prefixState_zero] using hq
  refine (loop_ok core (LoopInv orig A) (fun k q hk hq => ?_)
    (fun k q _ hk hq => ?_) q hi).mono fun t ht => ?_
  · unfold body
    rw [WP.block_append_iff]
    refine (hcore orig (prefixState A k) k q hp hq.1).mono fun u hu => ?_
    refine (iotaAdvance_ok orig _ k u hp hk hu).mono fun v hv => ?_
    refine ⟨?_,fun _ => hv.2⟩
    have he : Spec.Sha3.iota (Spec.Sha3.chi (Spec.Sha3.pi
        (Spec.Sha3.rho (Spec.Sha3.theta (prefixState A k))))) k = prefixState A (k + 1) := by
      rw [prefixState_succ]
      rfl
    simpa only [he] using hv.1
  · change eval (.nonzero .x .x27) q = _
    rw [eval_nonzero,hq.2 (by assumption),constAddr_test orig k hk]
  · simpa only [prefixState_final] using ht.1.core

end VG.Proof.Sha3.AArch64.Scalar.Control
