import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.Block

/-!
# x86 (32-bit): lemmas for symbolic execution
-/

namespace VG.X86

/-- The address `[x + d]`, as the model computes it. -/
def addr (x : BitVec 32) (d : Nat) : Addr := (x + BitVec.ofNat 32 d).setWidth 64

theorem ea_mk (s : State) (b : Reg) (d : Nat) : s.ea ⟨b, d⟩ = addr (s.gpr b) d := rfl

/-- Addresses do not wrap. -/
theorem addr_eq {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr x k = x.setWidth 64 + BitVec.ofNat 64 k := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k) h,
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega)]

theorem bswap_readW (m : Mem) (a : Addr) :
    bswap (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  byteRev32_readW m a

/-! Symbolic execution of a block, one instruction at a time (see `runStep`).
These are deliberately not proved by `rfl`: `simp` would use an `rfl` lemma
as a definitional unfolding, which the kernel then re-checks by unfolding the
structural recursion of `runBlock` over the whole remaining block, at every
instruction. -/

theorem runBlock_nil {s : State} : runBlock isa ([] : List Instr) s = some s := by
  rw [runBlock]

theorem runBlock_cons {i : Instr} {is : List Instr} {s : State} :
    runBlock isa (i :: is : List Instr) s = runStep isa (exec i s) is := by
  rw [runBlock]; rfl

theorem runStep_some {s : State} {is : List Instr} :
    runStep isa (some s : Option State) is = runBlock isa is s := by
  rw [runStep]; rfl

end VG.X86
