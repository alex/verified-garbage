import VerifiedGarbage.Impl.Ecdsa.X86_64

/-!
# ECDH on x86-64

`vg_ecdh_<curve>(out = rdi, d = rsi, peer = rdx, scratch = rcx) -> eax`,
for a curve of `n` 64-bit words, from the code of ECDSA's signature
(`Impl/Ecdsa/X86_64.lean`), whose layout of the working space it uses:

1. `scratch` to `r8`, `peer` to `r9`, `d`'s pointer to `rcx` (the
   signature's `k`) and `peer + 1` to `rdx` (its hash); then the
   signature's setup and tables of bits, unchanged: `d` is read into the
   slots of `k` and `d`, the peer's `x` into that of the hash;
2. `R² mod p` and `b R mod p` to slots of their own, the peer's `y` to
   another, and into the flag the masks of the peer's first byte being
   `04`, `x < p` and `y < p`;
3. `x` and `y` into Montgomery's form, and the mask of `y² = x³ + a x + b`
   into the flag;
4. the peer's point, or `G` if the flag is clear (so the ladder always runs
   on a point of the curve), to the slots the ladder takes its point from;
5. `[d]P` by the signature's ladder, and `Z^(p-2)` by its power;
6. `x = X Z^(p-2)`, out of Montgomery's form, and the masks of `d` in
   `[1, n-1]` and `Z ≠ 0` into the flag, which selects `x` or zeros for
   `out` (big-endian) and is returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers may affect
timing (the contract would let the peer's public key affect it too).
-/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-! Slots of the signature's layout, as ECDH uses them. The hash's slot `E`
holds the peer's `x`. -/

/-- The peer's `y`. -/
def QY : Nat := RR
/-- `R² mod p`. -/
def R2P : Nat := DM
/-- `b R mod p`. -/
def BP : Nat := EM
/-- `x R mod p`. -/
def QXM : Nat := XM
/-- `y R mod p`. -/
def QYM : Nat := X
/-- Temporaries of the check that the peer's point is on the curve. -/
def W0 : Nat := KM
def W1 : Nat := TT
def W2 : Nat := SM
def W3 : Nat := RM
/-- The point the ladder multiplies: the peer's, or `G`. -/
def PX : Nat := RM
def PY : Nat := SS

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `scratch` to `r8`, `peer` to `r9`, `d`'s pointer to `rcx` and
`peer + 1` to `rdx`: the signature's arguments, with `k` and `d` both `d`
and the hash the peer's `x`. -/
def args : List Instr :=
  [.mov .r8 (.reg .rcx), .mov .r9 (.reg .rdx), .mov .rcx (.reg .rsi), .alu .add .rdx (.imm 1)]

/-- The signature's setup and tables of bits. -/
def prefix' : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- The constants ECDH adds to the signature's. -/
def consts : List (Nat × Nat) := [(R2P, c.R * c.R % c.C.p), (BP, c.mont c.C.b)]

/-- The mask `rax` of `[a] < p` (all ones if it is), through `rdx`. -/
def ltP (a : Nat) : List Instr :=
  ((List.range c.n).flatMap fun j =>
    [.mov .rdx (.mem (sc (a + 8 * j))), .alu (if j = 0 then .sub else .sbb) .rdx (.mem (sc (c.sl MP + 8 * j)))]) ++
  [.alu .sbb .rax (.reg .rax)]

/-- `[a] < p`: the flag `&=` its mask. -/
def checkLtP (a : Nat) : List Instr := ltP c a ++ [.mov .rdx (.reg .rax)] ++ c.andFlag

/-- The mask `rdx` of `[a] = 0` (all ones if it is). -/
def zero (a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc a))] ++ ((List.range (c.n - 1)).map fun j => .alu .or .rdx (.mem (sc (a + 8 * (j + 1))))) ++
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)]

/-- `[a] = 0`: the flag `&=` its mask. -/
def checkZero (a : Nat) : List Instr := zero c a ++ c.andFlag

/-- The peer's first byte is `04`: the flag `&=` its mask. -/
def checkLead : List Instr :=
  [.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4), .alu .cmp .rdx (.imm 1),
    .alu .sbb .rdx (.reg .rdx)] ++ c.andFlag

/-- The constants, the peer's `y`, and the checks of its first byte, `x`
and `y`. -/
def peer : List Instr :=
  (consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  [.mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 (1 + 8 * c.n)))] ++
  loadBE c.n (c.sl QY) .rdx ++ checkLead c ++ checkLtP c (c.sl E) ++ checkLtP c (c.sl QY)

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl QYM) (c.sl QYM), .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM), .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl W3) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- The point to the ladder's slots: the peer's if the flag is set, else
`G`. -/
def select : List Instr :=
  [.mov .rcx (.mem (sc (c.sl FLAG)))] ++
  sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)

/-- `x` and `y` into Montgomery's form, the check that the point is on the
curve, and the point the ladder multiplies. -/
def validate : Prog isa :=
  blocks ([Mont.X86_64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P),
    Mont.X86_64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)] ++
    (curveOps c).map (FOp.code c.MP') ++ [checkZero c (c.sl W1) ++ select c])

/-- The ladder of the signature, from the point at `PX`, `PY`, `ONEP`. -/
def ladderQ : LadderCfg := { c.ladderCfg with G := c.pt PX PY ONEP }

/-- `x` (or zeros) to `out`, the flag's low bit to `rax`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .rcx (.mem (sc (c.sl FLAG)))] ++ storeBE c.n .r14 0 (c.sl X) ++
  [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] ++
  Impl.Ecdsa.X86_64.Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, the checks
of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  blocks [Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c]

/-- `vg_ecdh_<curve>`. -/
def exchange : Prog isa :=
  .seq (.block (args)) <| .seq (prefix' c) <| .seq (.block (peer c)) <| .seq (validate c) <|
  .seq (ladder (ladderQ c)) <| .seq (pow c.powP) (middle c)

end Cfg

end VG.Impl.Ecdh.X86_64
