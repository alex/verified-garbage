import VerifiedGarbage.Proof.Md5.X86.Shared
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.TCB.Axioms

/-! `Verified.stackScratch` on a real function with its arguments on the
stack: MD5's `update` on x86 (its streaming code and its proofs as they are)
without its scratch argument. The scratch-less signature and contract are
local to this test. -/

namespace VG.Test.StackScratchX86

open VG.Spec.Md5

/-- `vg_md5_update` without `scratch`. -/
def updateSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

def updatePost : updateSig.Post X86.abi.ptrBits := fun state count data len m m' _ =>
  ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
    Repr m' state (msg ++ bytesAt m data len.toNat)

def updateContract (stack : Nat) : Contract X86.isa :=
  updateSig.contract X86.abi (post := updatePost) (writeArgs := true) (stack := stack)

-- The contract with the scratch argument is `Sig.scratchContract` of the one
-- without it.
example : Spec.Md5.updateContract X86.abi 20 =
    Sig.scratchContract X86.abi updateSig "scratch" .u64 14 (Curry.const (fun _ => True) _) updatePost
      true 20 := rfl

/-- The postcondition reads the memory on entry only in the buffers. -/
theorem updatePost_local : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words X86.abi.ptrBits) updatePost vs m₁ m' r →
      Curry.apply (updateSig.words X86.abi.ptrBits) updatePost vs m₂ m' r
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
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int X86.abi.ptrBits).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth 32).toNat from Proof.Md5.Stream.bytesAt_congr hd]
    exact h msg (Proof.Md5.Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

/-- A state satisfying the precondition: `update`'s, but with its arguments
writable and no scratch argument. -/
def sat : X86.State :=
  { Proof.MdStream.X86.Update.sat₀ with rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 80⟩, ⟨0x5004, 20⟩] }

theorem update : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 140 5 Impl.Md5.X86.Stream.update)
    (updateContract (20 + 140)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 20) (bytes := 140)
    Proof.Md5.X86.Shared.update (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) updatePost_local
    (by implies_sat [updateContract, updateSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [sat, Proof.MdStream.X86.Update.sat₀, Proof.MdStream.X86.Update.satMem, X86.arg, X86.argAddr,
        Mem.readW, Mem.read] using sat)

#assert_standard_axioms update

end VG.Test.StackScratchX86
