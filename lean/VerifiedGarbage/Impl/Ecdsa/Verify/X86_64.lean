import VerifiedGarbage.Impl.Ecdh.X86_64

/-!
# ECDSA signature verification on x86-64

`vg_ecdsa_<curve>_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx) -> eax`, for a curve of `n` 64-bit words, from the code of
ECDSA's signature (`Impl/Ecdsa/X86_64.lean`) and of ECDH
(`Impl/Ecdh/X86_64.lean`), whose layout of the working space it uses:

1. `scratch` to `r8`, `public` to `r9`, `sig` to `rcx` (the signature's
   `k`), `public + 1` to `rdx` (its hash) and `sig + 8 n` to `r10`; then
   the signature's setup and tables of bits, unchanged: `r` is read into
   the slot of `k`, the hash into that of `d`, the key's `x` into that of
   the hash; then `s` into `PT` (which only the powers use);
2. ECDH's checks of the key (`peer`, `validate`): its first byte, `x < p`,
   `y < p` and the curve's equation, into the flag, and the key's point, or
   `G` if the flag is clear, to the slots of ECDH's ladder;
3. the masks of `r` and `s` in `[1, n-1]` into the flag, and
   `w = s^(n-2)`, in Montgomery form modulo `n`;
4. `u = e w` and `v = r w` modulo `n`, out of Montgomery's form;
5. `[u]G` by the signature's ladder (from the table of `u`'s bits), saved
   to `U`, and `R` reset to `O`; then `[v]Q` by ECDH's ladder (from the
   table of `v`'s bits) and `[u]G + [v]Q` by the complete addition, into
   `R`;
6. `Z^(p-2)` by the signature's power, `x = X Z^(p-2)` out of Montgomery's
   form, and the masks of `Z ≠ 0` and `x R ≡ r R` modulo `n` into the
   flag, which is returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers affect
timing, although the contract would let every input affect it.
-/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-! Slots of the signature's layout, as verification uses them, after ECDH's
checks of the key: `K` holds `r`, `D` the hash and `PT` `s` (until the
power modulo `n`). -/

/-- `s R mod n`, the power's base. -/
def SM' : Nat := KM
/-- `e R mod n` and `r R mod n`. -/
def EM' : Nat := EM
def RM' : Nat := DM
/-- `u R` and `v R` modulo `n`, then `u` and `v`. -/
def UM : Nat := TT
def VM : Nat := SM
def U : Nat := XM
def V : Nat := X
/-- `[u]G`. -/
def UX : Nat := TT
def UY : Nat := SM
def UZ : Nat := KM
/-- `x R mod n`, and `x R - r R mod n`. -/
def XN : Nat := RM
def W : Nat := EM

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `scratch` to `r8`, `public` to `r9`, `sig` to `rcx`, `sig + 8 n` to
`r10` and `public + 1` to `rdx`: the signature's arguments, with `k` the
signature's `r`, `d` the hash and the hash the key's `x`. -/
def args : List Instr :=
  [.mov .r8 (.reg .rcx), .mov .r9 (.reg .rdi), .mov .rcx (.reg .rdx), .mov .r10 (.reg .rdx),
    .alu .add .r10 (.imm (BitVec.ofNat 32 (8 * c.n))), .mov .rdx (.reg .rdi), .alu .add .rdx (.imm 1)]

/-- `s`, into `PT`. -/
def loadS : List Instr := loadBE c.n (c.sl PT) .r10

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  blocks [c.checkRange (c.sl K) ++ c.checkRange (c.sl PT),
    Mont.X86_64.mul c.MN' (c.sl SM') (c.sl PT) (c.sl R2N)]

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  blocks [Mont.X86_64.mul c.MN' (c.sl EM') (c.sl D) (c.sl R2N),
    Mont.X86_64.mul c.MN' (c.sl RM') (c.sl K) (c.sl R2N),
    Mont.X86_64.mul c.MN' (c.sl UM) (c.sl EM') (c.sl ACC),
    Mont.X86_64.mul c.MN' (c.sl VM) (c.sl RM') (c.sl ACC),
    Mont.X86_64.mul c.MN' (c.sl U) (c.sl UM) (c.sl ONE),
    Mont.X86_64.mul c.MN' (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy c.n (c.sl UX) (c.sl RX) ++ copy c.n (c.sl UY) (c.sl RY) ++ copy c.n (c.sl UZ) (c.sl RZ) ++
  setConst c.n (c.sl RX) 0 ++ setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprogB c.MP' (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++ copy c.n (c.sl RY) (c.sl DY) ++
      copy c.n (c.sl RZ) (c.sl DZ)))

/-- The flag's low bit to `rax`, and the callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .rax (.mem (sc (c.sl FLAG))), .alu .and .rax (.imm 1)] ++
  Impl.Ecdsa.X86_64.Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  blocks [Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.X86_64.mul c.MN' (c.sl XN) (c.sl X) (c.sl R2N),
    Mont.X86_64.sub c.MN' (c.sl W) (c.sl XN) (c.sl RM'),
    c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.X86_64.Cfg.checkZero c (c.sl W) ++ finish c]

/-- `[u]G + [v]Q`, into `R`, from the tables of bits of `u` and `v`. -/
def points : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (ladder c.ladderCfg) <| .seq (.block (save c)) <|
  .seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n)) <| .seq (ladder (Impl.Ecdh.X86_64.Cfg.ladderQ c)) (sum c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq (pow c.powN) <| .seq (uv c) <| .seq (points c) <| .seq (pow c.powP) (final c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.validate c) (back c)

end Cfg

end VG.Impl.Ecdsa.Verify.X86_64
