import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_decaps`

`decaps(dk, ct, key, scratch) -> eax`: `ML-KEM.Decaps_internal(dk, c)`
(Algorithm 18), with `scratch` (argument 3) in `esi`:

* K-PKE.Decrypt (`decrypt`): `w = Σ ŝ[i] ×_T NTT(u'[i])` at `eU`, with `u'[i]`
  at `eA` and `ŝ[i]` at `eT`, then `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(w)))`
  into `eM`, with `v'` at `eE`;
* `ek` copied from `dk` into `eEK`, `(K', r') = G(m' ‖ h)` into `eKR`, and
  the ciphertext `c'` of `m'` computed by `encrypt` (`Encrypt.lean`);
* `K̄ = J(z ‖ c)` into `deKB`;
* `c` and `c'` compared (`cmpC`): the OR of the XORs of their bytes, 0 if
  and only if they are equal, gives a mask, all ones if they are and zero
  otherwise (`sub`, `sbb`), with no branch;
* `key = K̄ ^ ((K' ^ K̄) & mask)`, byte by byte (`selC`).

`eACC` is returned.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `K̄`. -/
def deKB : Nat := 15640

/-- `w ← ŝ[i] ×_T NTT(u'[i])`, or `w ← w + …` if `0 < i`. -/
def decTerm (i : Nat) : Prog isa :=
  .seq (ddC 3 10 ⟨1, 320 * i, 320⟩ ⟨3, eA, 1024⟩) <| .seq (nttC 3 ⟨3, eA, 1024⟩ ⟨3, eNS, 1024⟩) <|
  .seq (dec12C 3 ⟨0, 384 * i, 384⟩ ⟨3, eT, 1024⟩) <|
  if i = 0 then mulC 3 ⟨3, eU, 1024⟩ ⟨3, eT, 1024⟩ ⟨3, eA, 1024⟩ ⟨3, eNS, 1024⟩
  else .seq (mulC 3 ⟨3, eP, 1024⟩ ⟨3, eT, 1024⟩ ⟨3, eA, 1024⟩ ⟨3, eNS, 1024⟩) (addC 3 ⟨3, eU, 1024⟩ ⟨3, eP, 1024⟩)

/-- K-PKE.Decrypt(dk_PKE, c), into `scratch + eM`. -/
def decrypt : Prog isa :=
  .seq (decTerm 0) <| .seq (decTerm 1) <| .seq (decTerm 2) <|
  .seq (nttInvC 3 ⟨3, eU, 1024⟩ ⟨3, eNS, 1024⟩) <| .seq (ddC 3 4 ⟨1, 960, 128⟩ ⟨3, eE, 1024⟩) <|
  .seq (subC 3 ⟨3, eE, 1024⟩ ⟨3, eU, 1024⟩) (ceC 3 1 ⟨3, eE, 1024⟩ ⟨3, eM, 32⟩)

/-- `ebx ← ` all ones if `c = c'`, and zero otherwise: the OR of the XORs of
their bytes, through `edi` (`c`), `ebp` (`scratch`, then `c'` at `eC`), `ecx`,
`eax` and `edx`. -/
def cmpInit : List Instr :=
  [.mov .edi (.mem (at_ .esp 24)), .mov .ebp (.reg .esi), .mov .ecx (.imm 1088), .mov .ebx (.imm 0)]
def cmpBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .movzx8 .edx (at_ .ebp eC), .alu .xor .eax (.reg .edx), .alu .or .ebx (.reg .eax),
    .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]
def cmpEnd : List Instr := [.alu .sub .ebx (.imm 1), .alu .sbb .ebx (.reg .ebx)]
def cmpC : Prog isa := .seq (.block cmpInit) <| .seq (.loop (.block cmpBody) .ne) (.block cmpEnd)

/-- `key[k] ← K̄[k] ^ ((K'[k] ^ K̄[k]) & ebx)`, through `edi` (`scratch`, then
`K'` at `eKR` and `K̄` at `deKB`), `ebp` (`key`), `ecx`, `eax` and `edx`. -/
def selInit : List Instr := [.mov .edi (.reg .esi), .mov .ebp (.mem (at_ .esp 28)), .mov .ecx (.imm 32)]
def selBody : List Instr :=
  [.movzx8 .eax (at_ .edi eKR), .movzx8 .edx (at_ .edi deKB), .alu .xor .eax (.reg .edx),
    .alu .and .eax (.reg .ebx), .alu .xor .eax (.reg .edx), .store8 (at_ .ebp 0) .al,
    .alu .add .edi (.imm 1), .alu .add .ebp (.imm 1), .alu .sub .ecx (.imm 1)]
def selC : Prog isa := .seq (.block selInit) (.loop (.block selBody) .ne)

def decapsBody : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
  .seq decrypt <|
  .seq (copyW 3 ⟨0, 1152, 1184⟩ ⟨3, eEK, 1184⟩ 296) <|
  .seq (hash2 3 eST eWK 72 6 ⟨3, eM, 32⟩ ⟨0, 2336, 32⟩ ⟨3, eKR, 64⟩) <|
  .seq (encrypt 3) <|
  .seq (hash2 3 eST eWK 136 0x1f ⟨0, 2368, 32⟩ ⟨1, 0, 1088⟩ ⟨3, deKB, 32⟩) <|
  .seq cmpC <| .seq selC (.block [.mov .eax (.mem (at_ .esi eACC))])

def decaps : Prog isa := leaf decapsBody

end VG.Impl.MlKem.X86
