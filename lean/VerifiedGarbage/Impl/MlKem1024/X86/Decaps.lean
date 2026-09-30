import VerifiedGarbage.Impl.MlKem1024.X86.Encrypt
import VerifiedGarbage.Impl.MlKem.X86.Decaps

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_decaps`

`decaps(dk, ct, key, scratch) -> eax`: `ML-KEM.Decaps_internal(dk, c)`
(Algorithm 18), as `vg_mlkem768_decaps` (`Impl/MlKem/X86/Decaps.lean`), with
`scratch` (argument 3) in `esi`:

* K-PKE.Decrypt (`decrypt4`): `w = Σ ŝ[i] ×_T NTT(u'[i])` at `e4U`, with `u'[i]`
  at `e4A` and `ŝ[i]` at `e4T`, then `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(w)))`
  into `e4M`, with `v'` at `e4E`;
* `ek` copied from `dk` into `e4EK`, `(K', r') = G(m' ‖ h)` into `e4KR`, and
  the ciphertext `c'` of `m'` computed by `encrypt4` (`Encrypt.lean`);
* `K̄ = J(z ‖ c)` into `de4KB`;
* `c` and `c'` compared (`cmp4C`): the OR of the XORs of their bytes, 0 if
  and only if they are equal, gives a mask, all ones if they are and zero
  otherwise (`sub`, `sbb`), with no branch;
* `key = K̄ ^ ((K' ^ K̄) & mask)`, byte by byte (`sel4C`).

`e4ACC` is returned.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- `K̄`. -/
def de4KB : Nat := 17528

/-- `w ← ŝ[i] ×_T NTT(u'[i])`, or `w ← w + …` if `0 < i`. -/
def dec4Term (i : Nat) : Prog isa :=
  .seq (ddC1024 3 11 ⟨1, 352 * i, 352⟩ ⟨3, e4A, 1024⟩) <| .seq (nttC 3 ⟨3, e4A, 1024⟩ ⟨3, e4NS, 1024⟩) <|
  .seq (dec12C 3 ⟨0, 384 * i, 384⟩ ⟨3, e4T, 1024⟩) <|
  if i = 0 then mulC 3 ⟨3, e4U, 1024⟩ ⟨3, e4T, 1024⟩ ⟨3, e4A, 1024⟩ ⟨3, e4NS, 1024⟩
  else .seq (mulC 3 ⟨3, e4P, 1024⟩ ⟨3, e4T, 1024⟩ ⟨3, e4A, 1024⟩ ⟨3, e4NS, 1024⟩)
    (addC 3 ⟨3, e4U, 1024⟩ ⟨3, e4P, 1024⟩)

/-- K-PKE.Decrypt(dk_PKE, c), into `scratch + e4M`. -/
def decrypt4 : Prog isa :=
  .seq (dec4Term 0) <| .seq (dec4Term 1) <| .seq (dec4Term 2) <| .seq (dec4Term 3) <|
  .seq (nttInvC 3 ⟨3, e4U, 1024⟩ ⟨3, e4NS, 1024⟩) <| .seq (ddC1024 3 5 ⟨1, 1408, 160⟩ ⟨3, e4E, 1024⟩) <|
  .seq (subC 3 ⟨3, e4E, 1024⟩ ⟨3, e4U, 1024⟩) (ceC 3 1 ⟨3, e4E, 1024⟩ ⟨3, e4M, 32⟩)

/-- `ebx ← ` all ones if `c = c'`, and zero otherwise: the OR of the XORs of
their bytes, through `edi` (`c`), `ebp` (`scratch`, then `c'` at `e4C`), `ecx`,
`eax` and `edx`. -/
def cmp4Init : List Instr :=
  [.mov .edi (.mem (at_ .esp 24)), .mov .ebp (.reg .esi), .mov .ecx (.imm 1568), .mov .ebx (.imm 0)]
def cmp4Body : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .movzx8 .edx (at_ .ebp e4C), .alu .xor .eax (.reg .edx), .alu .or .ebx (.reg .eax),
    .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]
def cmp4C : Prog isa := .seq (.block cmp4Init) <| .seq (.loop (.block cmp4Body) .ne) (.block cmpEnd)

/-- `key[k] ← K̄[k] ^ ((K'[k] ^ K̄[k]) & ebx)`, through `edi` (`scratch`, then
`K'` at `e4KR` and `K̄` at `de4KB`), `ebp` (`key`), `ecx`, `eax` and `edx`. -/
def sel4Body : List Instr :=
  [.movzx8 .eax (at_ .edi e4KR), .movzx8 .edx (at_ .edi de4KB), .alu .xor .eax (.reg .edx),
    .alu .and .eax (.reg .ebx), .alu .xor .eax (.reg .edx), .store8 (at_ .ebp 0) .al,
    .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]
def sel4C : Prog isa := .seq (.block selInit) (.loop (.block sel4Body) .ne)

def decaps4Body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
  .seq decrypt4 <|
  .seq (copyW 3 ⟨0, 1536, 1568⟩ ⟨3, e4EK, 1568⟩ 392) <|
  .seq (hash2 3 e4ST e4WK 72 6 ⟨3, e4M, 32⟩ ⟨0, 3104, 32⟩ ⟨3, e4KR, 64⟩) <|
  .seq (encrypt4 3) <|
  .seq (hash2 3 e4ST e4WK 136 0x1f ⟨0, 3136, 32⟩ ⟨1, 0, 1568⟩ ⟨3, de4KB, 32⟩) <|
  .seq cmp4C <| .seq sel4C (.block [.mov .eax (.mem (at_ .esi e4ACC))])

def decaps : Prog isa := leaf decaps4Body

end VG.Impl.MlKem1024.X86
