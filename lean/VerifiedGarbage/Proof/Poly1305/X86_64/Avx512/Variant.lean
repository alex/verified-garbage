import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks

/-!
# `vg_poly1305_blocks_avx512` as an implementation of `vg_poly1305_blocks`

Untrusted: everything here is checked by Lean. The `BlocksImpl` of
`vg_poly1305_blocks_avx512` (see `Proof/Poly1305/X86_64/Variant.lean`): its
calls use 16 bytes of stack below its return address (the return addresses
of its call of `vg_poly1305_blocks_avx2` and of that one's call of
`vg_poly1305_blocks`), two levels of calls.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

namespace BlocksImpl

theorem avx512_keeps : ((instrs Impl.Poly1305.X86_64.Avx512.blocksAvx512).all fun i =>
    !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx512_nosp : NoSp Impl.Poly1305.X86_64.Avx512.blocksAvx512 :=
  fun i hi => by simpa using List.all_eq_true.mp avx512_keeps i hi

/-- The AVX-512 implementation, `vg_poly1305_blocks_avx512`. -/
def avx512 : BlocksImpl where
  name := Impl.Poly1305.X86_64.Blocks.name .avx512
  code := Impl.Poly1305.X86_64.Blocks.code .avx512
  stack := 16
  stack_le := by decide
  depth_le := by
    change Impl.Poly1305.X86_64.Avx512.blocksAvx512.depth ≤ 2
    lit_decide
  ok := Avx512.blocksAvx512_ok
  ct := Avx512.blocksAvx512_ct
  nosp := avx512_nosp
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512"
  features := Impl.Poly1305.X86_64.Blocks.features .avx512

end BlocksImpl

end VG.Proof.Poly1305.X86_64
