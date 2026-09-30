import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
import VerifiedGarbage.Impl.MlKem.X86_64.Decaps

/-!
# ML-KEM-768 on x86-64 with expanded encapsulation keys

An expanded encapsulation key (`Spec/MlKem/Expanded.lean`) is `ek`, then
`H(ek)` at byte 1184, then the nine entries of `Â` from byte 1216, each
1 KiB: the same polynomials `vg_mlkem768_keygen` samples to polynomials
6–14 of its working space (`aS`). So the functions here are those of
`KeyGen.lean`, `Encaps.lean` and `Decaps.lean`, with copies of `Â` and
`H(ek)` between the expanded key and the working space (`copy16`, 16 bytes
at a time) in place of sampling and hashing:

* `keyGenX`: `vg_mlkem768_keygen` (with `ekx` in `r12`, where it writes
  `ek`), then `H(ek)` (which it writes to `dk`) and `Â` to `ekx`;
* `expandEk(ek = rdi, ekx = rsi, scratch = rdx) -> eax`: `ek` to `ekx`,
  `H(ek)` to `ekx`, `ρ` to `SB`, `Â` sampled as in `vg_mlkem768_keygen`,
  and copied to `ekx`; it keeps `scratch` in `rbx`, `ek` in `rbp` and `ekx`
  in `r12`;
* `encapsX`: `vg_mlkem768_encaps` (with `ekx` in `r14`, where `ek` is),
  with `H(ek)` copied from `ekx` rather than computed, and `Â` copied to
  the working space rather than sampled;
* `decapsX(dk = rdi, ekx = rsi, ct = rdx, key = rcx, scratch = r8)`:
  `vg_mlkem768_decaps`, with `Â` copied from `ekx` (in `r13`) to the
  working space first rather than sampled after `G(m' ‖ h)`: K-PKE.Decrypt
  and the hashes use neither `r13` nor polynomials 6–14. (`r13` holds a
  buffer the function writes, in the other functions, so it may hold `ekx`
  only until `ekx`'s last use.)

`encapsX` and `decapsX` sample nothing, so they never fail: they return
`r15`, which stays 1.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- Copy `16 n` bytes from `src` to `dst`, 16 at a time (`n > 0`). -/
def copy16 (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 n))]))
    (.loop (.block [.movdquLoad .xmm0 (at_ .rsi 0), .movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16),
      .alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]) .ne)

/-- The offset of `H(ek)` in an expanded key. -/
def oXH : Nat := 1184

/-- The offset of `Â` in an expanded key. -/
def oXA : Nat := 1216

/-- `Â` from the working space to the expanded key at `x`. -/
def matOut (x : Reg) : Prog isa := copy16 (x, oXA) (aS 0 0) 576

/-- `Â` from the expanded key at `x` to the working space. -/
def matIn (x : Reg) : Prog isa := copy16 (aS 0 0) (x, oXA) 576

open KeyGen in
/-- `vg_mlkem768_keygen_expanded(seed = rdi, ekx = rsi, dk = rdx, scratch = rcx) -> eax`. -/
def keyGenX (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq gRho (.seq (samples c) (.seq (ifOk (.seq rest
    (.seq (copy (.r12, oXH) (.r13, 2336) 32) (matOut .r12)))) (.block topEpi))))

namespace ExpandEk

def pro : List Instr := topPro .rdx [(.rbp, .rdi), (.r12, .rsi)]

/-- `ek` and `H(ek)` to `ekx`, and `ρ` to `SB`. -/
def hash : Prog isa :=
  .seq (copy16 (.r12, 0) (.rbp, 0) 74) (.seq (hashAt [((.rbp, 0), 1184)] 136 6 (.r12, oXH) 32)
    (copy (sc oSB) (.rbp, 1152) 32))

end ExpandEk

open ExpandEk in
/-- `vg_mlkem768_expand_ek(ek = rdi, ekx = rsi, scratch = rdx) -> eax`. -/
def expandEk (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq hash (.seq (samples c) (.seq (ifOk (matOut .r12)) (.block topEpi))))

namespace EncapsX

open Encaps (pro out)

/-- `m` to `M`, `H(ek)` from `ekx` to `H`, and `G(m ‖ H(ek))`. -/
def hashes : Prog isa :=
  .seq (copy (sc oM) (.rbp, 0) 32) (.seq (copy (sc oH) (.r14, oXH) 32)
    (hashAt [(sc oM, 32), (sc oH, 32)] 72 6 (sc oG) 64))

end EncapsX

open Encaps (pro out) in
open EncapsX in
/-- `vg_mlkem768_encaps_expanded(ekx = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8)`. -/
def encapsX : Prog isa :=
  .seq (.block pro) (.seq hashes (.seq (matIn .r14) (.seq (Encrypt.rest (.r14, 0)) (.seq out (.block topEpi)))))

namespace DecapsX

def pro : List Instr := topPro .r8 [(.rbp, .rdi), (.r13, .rsi), (.r14, .rdx), (.r12, .rcx)]

end DecapsX

open Decaps (decrypt hashes select) in
/-- `vg_mlkem768_decaps_expanded(dk = rdi, ekx = rsi, ct = rdx, key = rcx, scratch = r8)`. -/
def decapsX : Prog isa :=
  .seq (.block DecapsX.pro) (.seq (matIn .r13) (.seq decrypt (.seq hashes
    (.seq (Encrypt.rest (.rbp, 1152)) (.seq select (.block topEpi))))))

end VG.Impl.MlKem.X86_64
