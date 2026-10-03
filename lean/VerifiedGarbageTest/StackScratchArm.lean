import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.TCB.Axioms

/-! `Verified.stackScratch` on a real function with its scratch argument on
the stack: MD5's `update` on ARMv7 (its streaming code and its proofs as they
are) without its scratch argument. `data` and `len` stay on the stack, and the
wrapper copies them into its frame. The scratch-less signature and contract
are local to this test. -/

namespace VG.Test.StackScratchArm

open VG.Spec.Md5

/-- `vg_md5_update` without `scratch`. -/
def updateSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

def updatePost : updateSig.Post Arm.abi.ptrBits := fun state count data len m m' _ =>
  ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
    Repr m' state (msg ++ bytesAt m data len.toNat)

def updateContract (stack : Nat) : Contract Arm.isa :=
  updateSig.contract Arm.abi (post := updatePost) (writeArgs := true) (stack := stack)

-- The contract with the scratch argument is `Sig.scratchContract` of the one
-- without it.
example : Spec.Md5.updateContract Arm.abi =
    Sig.scratchContract Arm.abi updateSig "scratch" .u64 14 (Curry.const (fun _ => True) _) updatePost
      true 0 := rfl

/-- The postcondition reads the memory on entry only in the buffers. -/
theorem updatePost_local : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words Arm.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words Arm.abi.ptrBits) updatePost vs m₁ m' r →
      Curry.apply (updateSig.words Arm.abi.ptrBits) updatePost vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 80, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth 32).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ 32)
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int Arm.abi.ptrBits).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth 32).toNat from Proof.Md5.Stream.bytesAt_congr hd]
    exact h msg (Proof.Md5.Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

/-- A state satisfying the precondition: no data, the state at `0x1000`, and
`data` and `len` on the stack at `0x4000`. -/
def sat : Arm.State :=
  { Proof.MdStream.Arm.Update.sat Impl.Md5.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 80⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update)
    (updateContract (0 + 128)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 0) (bytes := 128)
    (m := 2) Proof.Md5.Arm.Shared.update (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) updatePost_local
    (by implies_sat [updateContract, updateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      [sat, Proof.MdStream.Arm.Update.sat, Impl.Md5.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr,
        Mem.readW, Mem.read] using sat)

#assert_standard_axioms update

end VG.Test.StackScratchArm
