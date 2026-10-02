import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt

/-!
# ML-KEM on x86-64: encapsulation (`vg_mlkem768_encaps`, `vg_mlkem1024_encaps`)

`kemEncaps L (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`:
`ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17) of the parameter set
`L`. It keeps `scratch` in `rbx`, `m` in `rbp`, `key` in `r12`, `ct` in `r13`
and `ek` in `r14`, and saves its caller's values of them (and of `r15`) in
`scratch`.

1. `m` to `M`; `H(ek)` to `H`; `(K, r) = G(m ‖ H(ek))` to `G`.
2. `c = K-PKE.Encrypt(ek, m, r)` to `CT` (`Encrypt.lean`).
3. `K` to `key` and `c` to `ct`.

It returns `r15`: 0 if a `SampleNTT` failed (when `key` and `ct` are
unspecified), and 1 otherwise.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encaps

variable (L : Kem)

def pro : List Instr := topPro .r8 [(.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]

/-- `m` to `M`, `H(ek)` to `H`, and `G(m ‖ H(ek))`. -/
def hashes : Prog isa :=
  .seq (copy (sc oM) (.rbp, 0) 32) (.seq (hashAt [((.r14, 0), L.ekLen)] 136 6 (sc oH) 32)
    (hashAt [(sc oM, 32), (sc oH, 32)] 72 6 (sc oG) 64))

/-- `K` to `key` and `c` to `ct`. -/
def out : Prog isa := .seq (copy (.r12, 0) (sc oG) 32) (copy (.r13, 0) (sc L.oCT) L.ctLen)

end Encaps

open Encaps in
/-- The encapsulation of the parameter set `L`. -/
def kemEncaps (L : Kem) (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (hashes L) (.seq (encrypt L c (.r14, 0)) (.seq (out L) (.block topEpi))))

/-- `vg_mlkem768_encaps`. -/
abbrev encaps (c : Callee4) : Prog isa := kemEncaps kem768 c

end VG.Impl.MlKem.X86_64
