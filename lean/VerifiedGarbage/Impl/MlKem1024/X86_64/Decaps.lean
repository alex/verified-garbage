import VerifiedGarbage.Impl.MlKem1024.X86_64.Encrypt
import VerifiedGarbage.Impl.MlKem.X86_64.Decaps

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps`

`decaps1024(dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`:
`ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm 18) of ML-KEM-1024, as
`vg_mlkem768_decaps` (`Impl/MlKem/X86_64/Decaps.lean`, whose loop bodies it
shares): the same registers and saves.

1. `m' = K-PKE.Decrypt(dk[0 : 1536], c)` (Algorithm 15) to `M`:
   `u'[i] = Decompress₁₁(ByteDecode₁₁(c[352i : 352i + 352]))`, its NTT
   (polynomial `i`); `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`
   (polynomial `4 + i`); `w = v' - NTT⁻¹(ŝ[0] û[0] + ⋯ + ŝ[3] û[3])` with
   `v' = Decompress₅(ByteDecode₅(c[1408 : 1568]))` (polynomial 16), and
   `m' = ByteEncode₁(Compress₁(w))`.
2. `(K', r') = G(m' ‖ h)` to `G`, with `h = dk[3104 : 3136]`, and
   `K̄ = J(z ‖ c)` to `KB`, with `z = dk[3136 : 3168]`.
3. `c' = K-PKE.Encrypt(ek, m', r')` to `CT` (`Encrypt.lean`), with `ek` at
   `dk + 1536`.
4. The key `K'` if `c = c'`, and `K̄` otherwise, to `key`, without a branch,
   as `vg_mlkem768_decaps` chooses it (over the 1568 bytes of the
   ciphertexts).

It returns `r15`: 0 if a `SampleNTT` failed (when `key` is unspecified), and
1 otherwise.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

namespace Decaps1024

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]

/-- `NTT(u'[i])`. -/
def uHat (A : Arith) (i : Nat) : Prog isa := .seq (dd4At (.r14, 352 * i) 11 (pS i)) (nttAt A (pS i))

/-- `ŝ[i]`. -/
def sHat (i : Nat) : Prog isa := dec12At (.rbp, 384 * i) (pS (4 + i))

/-- `m'` to `M`. -/
def decrypt (A : Arith) : Prog isa :=
  .seq (seqR (uHat A) 0 4) (.seq (seqR sHat 0 4) (.seq (dot4At A (fun j => pS (4 + j)) pS)
    (.seq (nttInvAt A (pS 15)) (.seq (dd4At (.r14, 1408) 5 (pS 16)) (.seq (subAt (pS 16) (pS 15))
      (ceAt (pS 16) 1 (sc oM)))))))

/-- `G(m' ‖ h)` and `J(z ‖ c)`. -/
def hashes : Prog isa :=
  .seq (hashAt [(sc oM, 32), ((.rbp, 3104), 32)] 72 6 (sc oG) 64)
    (hashAt [((.rbp, 3136), 32), ((.r14, 0), 1568)] 136 0x1f (sc oKB) 32)

/-- The key `K'` if `c = c'`, and `K̄` otherwise. -/
def select : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oCT4)),
      .mov32 .rcx (.imm 1568), .mov32 .rdx (.imm 0)])
    (.seq (.loop Decaps.cmpBody .ne)
      (.seq (.block [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
          .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
          .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)])
        (.loop Decaps.selBody .ne)))

end Decaps1024

open Decaps1024 in
def decaps1024 (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (decrypt c.arith) (.seq hashes (.seq (encrypt1024 c (.rbp, 1536)) (.seq select (.block topEpi)))))

end VG.Impl.MlKem1024.X86_64
