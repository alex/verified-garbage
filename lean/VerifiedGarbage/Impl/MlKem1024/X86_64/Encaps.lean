import VerifiedGarbage.Impl.MlKem1024.X86_64.Encrypt

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_encaps`

`encaps1024(ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`:
`ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17) of ML-KEM-1024, as
`vg_mlkem768_encaps` (`Impl/MlKem/X86_64/Encaps.lean`): the same registers
and saves.

1. `m` to `M`; `H(ek)` to `H`; `(K, r) = G(m ‖ H(ek))` to `G`.
2. `c = K-PKE.Encrypt(ek, m, r)` to `CT` (`Encrypt.lean`).
3. `K` to `key` and `c` to `ct`.

It returns `r15`: 0 if a `SampleNTT` failed (when `key` and `ct` are
unspecified), and 1 otherwise.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

namespace Encaps1024

def pro : List Instr := topPro .r8 [(.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]

/-- `m` to `M`, `H(ek)` to `H`, and `G(m ‖ H(ek))`. -/
def hashes : Prog isa :=
  .seq (copy (sc oM) (.rbp, 0) 32) (.seq (hashAt [((.r14, 0), 1568)] 136 6 (sc oH) 32)
    (hashAt [(sc oM, 32), (sc oH, 32)] 72 6 (sc oG) 64))

/-- `K` to `key` and `c` to `ct`. -/
def out : Prog isa := .seq (copy (.r12, 0) (sc oG) 32) (copy (.r13, 0) (sc oCT4) 1568)

end Encaps1024

open Encaps1024 in
def encaps1024 (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq hashes (.seq (encrypt1024 c (.r14, 0)) (.seq out (.block topEpi))))

end VG.Impl.MlKem1024.X86_64
