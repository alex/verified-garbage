import VerifiedGarbage.Impl.MlKem1024.X86_64.KeyGen
import VerifiedGarbage.Impl.MlKem1024.X86_64.Encaps
import VerifiedGarbage.Impl.MlKem1024.X86_64.Decaps
import VerifiedGarbage.Impl.MlKem.X86_64.Expanded

/-!
# ML-KEM-1024 on x86-64 with expanded encapsulation keys

As `Impl/MlKem/X86_64/Expanded.lean` for ML-KEM-768. An expanded
encapsulation key (`Spec/MlKem/Expanded.lean`) is `ek`, then `H(ek)` at
byte 1568, then the sixteen entries of `Â` from byte 1600, each 1 KiB: the
polynomials `vg_mlkem1024_keygen` samples to polynomials 17–32 of its
working space (`aS4`). The functions are those of `KeyGen.lean`,
`Encaps.lean` and `Decaps.lean`, with copies of `Â` and `H(ek)` between the
expanded key and the working space (`copy16`) in place of sampling and
hashing:

* `keyGenX1024`: `vg_mlkem1024_keygen` (with `ekx` in `r12`, where it writes
  `ek`), then `H(ek)` (which it writes to `dk`) and `Â` to `ekx`;
* `expandEk1024(ek = rdi, ekx = rsi, scratch = rdx) -> eax`: `ek` and
  `H(ek)` to `ekx`, `Â` sampled as in `vg_mlkem1024_encaps`, and copied to
  `ekx`; it keeps `scratch` in `rbx`, `ek` in `rbp` and `ekx` in `r12`;
* `encapsX1024`: `vg_mlkem1024_encaps` (with `ekx` in `r14`, where `ek` is),
  with `H(ek)` copied from `ekx` rather than computed, and `Â` copied to
  the working space rather than sampled;
* `decapsX1024(dk = rdi, ekx = rsi, ct = rdx, key = rcx, scratch = r8)`:
  `vg_mlkem1024_decaps`, with `Â` copied from `ekx` (in `r13`) to the
  working space first rather than sampled after `G(m' ‖ h)`: K-PKE.Decrypt
  and the hashes use neither `r13` nor polynomials 17–32.

`encapsX1024` and `decapsX1024` sample nothing, so they never fail.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- The offset of `H(ek)` in an expanded key. -/
def oXH4 : Nat := 1568

/-- The offset of `Â` in an expanded key. -/
def oXA4 : Nat := 1600

/-- `Â` from the working space to the expanded key at `x`. -/
def matOut4 (x : Reg) : Prog isa := copy16 (x, oXA4) (aS4 0 0) 1024

/-- `Â` from the expanded key at `x` to the working space. -/
def matIn4 (x : Reg) : Prog isa := copy16 (aS4 0 0) (x, oXA4) 1024

open KeyGen1024 in
/-- `vg_mlkem1024_keygen_expanded(seed = rdi, ekx = rsi, dk = rdx, scratch = rcx) -> eax`. -/
def keyGenX1024 (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq gRho (.seq (samples4 c) (.seq (ifOk (.seq rest
    (.seq (copy (.r12, oXH4) (.r13, 3104) 32) (matOut4 .r12)))) (.block topEpi))))

namespace ExpandEk1024

def pro : List Instr := topPro .rdx [(.rbp, .rdi), (.r12, .rsi)]

/-- `ek` and `H(ek)` to `ekx`. -/
def hash : Prog isa :=
  .seq (copy16 (.r12, 0) (.rbp, 0) 98) (hashAt [((.rbp, 0), 1568)] 136 6 (.r12, oXH4) 32)

end ExpandEk1024

open ExpandEk1024 in
/-- `vg_mlkem1024_expand_ek(ek = rdi, ekx = rsi, scratch = rdx) -> eax`: `Â` as
`vg_mlkem1024_encaps` samples it (`Encrypt1024.mat`). -/
def expandEk1024 (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq hash (.seq (Encrypt1024.mat c (.rbp, 0)) (.seq (ifOk (matOut4 .r12)) (.block topEpi))))

namespace EncapsX1024

/-- `m` to `M`, `H(ek)` from `ekx` to `H`, and `G(m ‖ H(ek))`. -/
def hashes : Prog isa :=
  .seq (copy (sc oM) (.rbp, 0) 32) (.seq (copy (sc oH) (.r14, oXH4) 32)
    (hashAt [(sc oM, 32), (sc oH, 32)] 72 6 (sc oG) 64))

end EncapsX1024

open Encaps1024 (pro out) in
open EncapsX1024 in
/-- `vg_mlkem1024_encaps_expanded(ekx = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8)`. -/
def encapsX1024 : Prog isa :=
  .seq (.block pro) (.seq hashes (.seq (matIn4 .r14) (.seq (Encrypt1024.rest (.r14, 0)) (.seq out (.block topEpi)))))

namespace DecapsX1024

def pro : List Instr := topPro .r8 [(.rbp, .rdi), (.r13, .rsi), (.r14, .rdx), (.r12, .rcx)]

end DecapsX1024

open Decaps1024 (decrypt hashes select) in
/-- `vg_mlkem1024_decaps_expanded(dk = rdi, ekx = rsi, ct = rdx, key = rcx, scratch = r8)`. -/
def decapsX1024 : Prog isa :=
  .seq (.block DecapsX1024.pro) (.seq (matIn4 .r13) (.seq decrypt (.seq hashes
    (.seq (Encrypt1024.rest (.rbp, 1536)) (.seq select (.block topEpi))))))

end VG.Impl.MlKem1024.X86_64
