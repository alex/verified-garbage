import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_decaps`

`decaps(dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`:
`ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm 18). It keeps
`scratch` in `rbx`, `dk` in `rbp`, `ct` in `r14` and `key` in `r12`, and
saves its caller's values of them (and of `r13` and `r15`) in `scratch`.

1. `m' = K-PKE.Decrypt(dk[0 : 1152], c)` (Algorithm 15) to `M`:
   `u'[i] = Decompress₁₀(ByteDecode₁₀(c[320i : 320i + 320]))`, its NTT
   (polynomial `i`); `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`
   (polynomial `3 + i`); `w = v' - NTT⁻¹(ŝ[0] û[0] + ŝ[1] û[1] + ŝ[2] û[2])`
   with `v' = Decompress₄(ByteDecode₄(c[960 : 1088]))` (polynomial 7), and
   `m' = ByteEncode₁(Compress₁(w))`.
2. `(K', r') = G(m' ‖ h)` to `G`, with `h = dk[2336 : 2368]`, and
   `K̄ = J(z ‖ c)` to `KB`, with `z = dk[2368 : 2400]`.
3. `c' = K-PKE.Encrypt(ek, m', r')` to `CT` (`Encrypt.lean`), with `ek` at `dk + 1152`.
4. The key `K'` if `c = c'`, and `K̄` otherwise, to `key`, without a branch:
   `rdx` is the OR of the XORs of the bytes of `c` and `c'`, so 0 exactly
   when they are equal (`sub rdx, 1` borrows then), and `rax` the mask
   `-borrow`; each byte of `key` is `((K' ⊕ K̄) ∧ mask) ⊕ K̄`.

It returns `r15`: 0 if a `SampleNTT` failed (when `key` is unspecified), and
1 otherwise.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Decaps

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]

/-- `NTT(u'[i])`. -/
def uHat (A : Arith) (i : Nat) : Prog isa := .seq (ddAt (.r14, 320 * i) 10 (pS i)) (nttAt A (pS i))

/-- `ŝ[i]`. -/
def sHat (i : Nat) : Prog isa := dec12At (.rbp, 384 * i) (pS (3 + i))

/-- `m'` to `M`. -/
def decrypt (A : Arith) : Prog isa :=
  .seq (seqR (uHat A) 0 3) (.seq (seqR sHat 0 3) (.seq (dotAt A (fun j => pS (3 + j)) pS)
    (.seq (nttInvAt A (pS 15)) (.seq (ddAt (.r14, 960) 4 (pS 16)) (.seq (subAt (pS 16) (pS 15))
      (ceAt (pS 16) 1 (sc oM)))))))

/-- `G(m' ‖ h)` and `J(z ‖ c)`. -/
def hashes : Prog isa :=
  .seq (hashAt [(sc oM, 32), ((.rbp, 2336), 32)] 72 6 (sc oG) 64)
    (hashAt [((.rbp, 2368), 32), ((.r14, 0), 1088)] 136 0x1f (sc oKB) 32)

/-- The OR of the XORs of the bytes of `c` and `c'`, to `rdx`. -/
def cmpBody : Prog isa :=
  .block [.movzx8 .rax (at_ .rsi 0), .movzx8 .r8 (at_ .rdi 0), .alu .xor .rax (.reg .r8), .alu .or .rdx (.reg .rax),
    .alu .add .rsi (.imm 1), .alu .add .rdi (.imm 1), .alu .sub .rcx (.imm 1)]

/-- A byte of the key, `((K' ⊕ K̄) ∧ mask) ⊕ K̄`. -/
def selBody : Prog isa :=
  .block [.movzx8 .r9 (at_ .rsi 0), .movzx8 .r10 (at_ .rdi 0), .alu .xor .r9 (.reg .r10), .alu .and .r9 (.reg .rax),
    .alu .xor .r9 (.reg .r10), .store8 (at_ .r8 0) .r9, .alu .add .rsi (.imm 1), .alu .add .rdi (.imm 1),
    .alu .add .r8 (.imm 1), .alu .sub .rcx (.imm 1)]

/-- The key `K'` if `c = c'`, and `K̄` otherwise. -/
def select : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oCT)),
      .mov32 .rcx (.imm 1088), .mov32 .rdx (.imm 0)])
    (.seq (.loop cmpBody .ne)
      (.seq (.block [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
          .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
          .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)])
        (.loop selBody .ne)))

end Decaps

open Decaps in
def decaps (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (decrypt c.arith) (.seq hashes (.seq (encrypt c (.rbp, 1152)) (.seq select (.block topEpi)))))

end VG.Impl.MlKem.X86_64
