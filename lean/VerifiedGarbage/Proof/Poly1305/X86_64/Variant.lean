import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Impl.Poly1305.X86_64.Callee

/-!
# Implementations of `vg_poly1305_blocks` on x86-64

Untrusted: everything here is checked by Lean.

A `BlocksImpl` is what a function that calls `vg_poly1305_blocks` needs of
it, so that its proof holds for every implementation: each is a variant of
the interface `Poly1305Blocks` on x86-64 (`Variants/Poly1305Blocks/X86_64/`),
and each caller (in `Generic/Poly1305Blocks/X86_64/`) is emitted once for
each of them (see `TCB/Emit.lean`). Callers leave room for 16 bytes of stack
below its return address (`stack_le`), and for two levels of calls
(`depth_le`).

(ChaCha20-Poly1305 calls `vg_poly1305_blocks` too, but through the
implementation that goes with its implementation of `vg_chacha20_xor`,
`Proof.ChaCha20.X86_64.XorImpl.poly`.)
-/

namespace VG.Proof.Poly1305

open VG.X86_64 in
/-- `blocksX86_64` with `k` bytes of stack below the return address, for an
implementation whose calls use them: what callers of any implementation of
`vg_poly1305_blocks` rely on. -/
def blocksStack (k : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      stack.Disjoint state ∧ stack.Disjoint blocks ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post := Proof.Poly1305.blocksX86_64.post
  pub s₁ s₂ := Proof.Poly1305.blocksX86_64.pub s₁ s₂ ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

/-- An implementation of `vg_poly1305_blocks` on x86-64. -/
structure BlocksImpl where
  /-- Its symbol. -/
  name : String
  /-- Its code. -/
  code : Prog isa
  /-- The stack its calls use below its return address. -/
  stack : Nat
  stack_le : stack ≤ 16
  depth_le : code.depth ≤ 2
  /-- It is correct. -/
  ok : ∀ s, (blocksStack stack).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (blocksStack stack).post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa (blocksStack stack).pre (blocksStack stack).pub code
  /-- It never writes the stack pointer. -/
  nosp : NoSp code
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace BlocksImpl

theorem scalar_ok : ∀ s, (blocksStack 0).pre s → ∃ t s', Exec isa Impl.Poly1305.X86_64.blocks s t s' ∧
    abiPreserved s s' ∧ (blocksStack 0).post s s' :=
  fun s ⟨h1, h2, h3, h4, _, _, h7⟩ => blocks_ok s ⟨h1, h2, h3, h4, h7⟩

theorem scalar_ct : ConstantTime isa (blocksStack 0).pre (blocksStack 0).pub Impl.Poly1305.X86_64.blocks :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨a1, a2, a3, a4, _, _, a7⟩ ⟨b1, b2, b3, b4, _, _, b7⟩ hp e₁ e₂ =>
    blocks_ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨a1, a2, a3, a4, a7⟩ ⟨b1, b2, b3, b4, b7⟩ hp.1 e₁ e₂

/-- The scalar implementation, `vg_poly1305_blocks`, in the baseline ISA. -/
def scalar : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .scalar
  code := Impl.Poly1305.X86_64.Blocks.code .scalar
  stack := 0
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.blocks.depth ≤ 2
    rw [Avx2.blocks_depth]; decide
  ok := scalar_ok
  ct := scalar_ct
  nosp := Avx2.blocks_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := Impl.Poly1305.X86_64.Blocks.features .scalar

theorem avx2_keeps : ((instrs Impl.Poly1305.X86_64.Avx2.blocksAvx2).all fun i =>
    !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx2_nosp : NoSp Impl.Poly1305.X86_64.Avx2.blocksAvx2 :=
  fun i hi => by simpa using List.all_eq_true.mp avx2_keeps i hi

/-- The AVX2 implementation, `vg_poly1305_blocks_avx2`. -/
def avx2 : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .avx2
  code := Impl.Poly1305.X86_64.Blocks.code .avx2
  stack := 8
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth ≤ 2
    lit_decide
  ok := Avx2.blocksAvx2_ok
  ct := Avx2.blocksAvx2_ct
  nosp := avx2_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx2"
  features := Impl.Poly1305.X86_64.Blocks.features .avx2

end BlocksImpl

end VG.Proof.Poly1305.X86_64
