import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Spec.Gcm

/-!
# GHASH on x86-64: the contract of `vg_ghash`

Untrusted: everything here is checked by Lean. The contract alone, apart from
its proof (`Proof/Gcm/X86_64/Ghash.lean`), so that the callers of `vg_ghash`
need not import the algebra the proof uses.
-/

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.X86_64 in
/-- X86-64 contract for `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data:
*const [u8; 16], n: usize, scratch: *mut [u64; 32])`: replaces the block `Y` at
`y` with `GHASH_H` continued from `Y` over the `n` blocks at `data`, where `H`
is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other, the other
buffers, or the return address on the stack. The pointers and `n` are
public; `H`, `Y` and the data are secret. -/
def ghashX86_64 : Contract X86_64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .rdi, 16⟩
    let y : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ ret.Disjoint y ∧ ret.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .rsi) =
      ghashFrom (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
        (blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8
end VG.Proof.Gcm
