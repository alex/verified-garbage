import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86-64: the contracts of the compressions the proofs are written against

Untrusted: everything here is checked by Lean. As
`Proof/MlKem/X86_64/Contracts.lean`, for `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress`, whose widths are ML-KEM-1024's
(`Spec.MlKem1024.compressWidths`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem1024_compress_encode(f = rdi, d = esi, out = rdx, len = rcx)`. -/
def compressEncode1024K : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ dArg s .rsi ∈ Spec.MlKem1024.compressWidths ∧
    (s.gpr .rcx).toNat = 32 * dArg s .rsi ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    compressEncode (dArg s .rsi) (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mlkem1024_decode_decompress(b = rdi, len = rsi, d = edx, f = rcx)`. -/
def decodeDecompress1024K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .rcx)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    dArg s .rdx ∈ Spec.MlKem1024.compressWidths ∧ (s.gpr .rsi).toNat = 32 * dArg s .rdx
  post s s' := PolyIs s'.mem (s.gpr .rcx)
    (decodeDecompress (dArg s .rdx) (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

end VG.Proof.MlKem1024.X86_64
