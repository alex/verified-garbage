import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee

/-!
# Implementations of `vg_chacha20_xor` on x86-64

Untrusted: everything here is checked by Lean.

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on x86-64 (`Variants/ChaCha20Xor/X86_64/`), and each
caller (in `Generic/ChaCha20Xor/X86_64/`) is emitted once for each of them
(see `TCB/Emit.lean`). Callers leave room for 16 bytes of stack below its
return address (`stack_le`), and for two levels of calls (`depth_le`).
-/

namespace VG.Proof.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` on x86-64. -/
structure XorImpl where
  /-- Its symbol and code. -/
  callee : Impl.ChaCha20.X86_64.Callee
  /-- The stack its calls use below its return address. -/
  stack : Nat
  stack_le : stack ≤ 16
  depth_le : callee.code.depth ≤ 2
  /-- It is correct, and returns with `rsi` pointing at `buf`. -/
  ok : ∀ s, (xorStack stack).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (xorStack stack).post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa (xorStack stack).pre (xorStack stack).pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XorImpl

theorem scalar_ok : ∀ s, (xorStack 8).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.scalar.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 8).post s s' :=
  fun s hs => Xor.xor_rsi s hs

theorem scalar_ct : ConstantTime isa (xorStack 8).pre (xorStack 8).pub Impl.ChaCha20.X86_64.Callee.scalar.code :=
  Xor.xor_ct

/-- The scalar implementation, `vg_chacha20_xor`, in the baseline ISA. -/
def scalar : XorImpl where
  callee := .scalar
  stack := 8
  stack_le := by decide
  depth_le := by decide +kernel
  ok := scalar_ok
  ct := scalar_ct
  nosp := Avx2.xor_nosp
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

theorem avx2_ok : ∀ s, (xorStack 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx2.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 16).post s s' :=
  fun s hs => Avx2.xor_rsi s hs

theorem avx2_ct : ConstantTime isa (xorStack 16).pre (xorStack 16).pub Impl.ChaCha20.X86_64.Callee.avx2.code :=
  Avx2.xor_ct

theorem avx2_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx2.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx2.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The AVX2 implementation, `vg_chacha20_xor_avx2`. -/
def avx2 : XorImpl where
  callee := .avx2
  stack := 16
  stack_le := by decide
  depth_le := by decide +kernel
  ok := avx2_ok
  ct := avx2_ct
  nosp := avx2_nosp
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_avx2"
  features := ["avx", "avx2"]

end XorImpl

end VG.Proof.ChaCha20.X86_64
