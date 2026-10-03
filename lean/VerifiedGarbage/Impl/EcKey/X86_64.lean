import VerifiedGarbage.Impl.Ecdsa.X86_64

/-!
# Elliptic curve public keys on x86-64

`vg_ec_<curve>_public_key(out = rdi, d = rsi, scratch = rdx) -> eax`, for a
curve of `n` 64-bit words, from the code of ECDSA's signature
(`Impl/Ecdsa/X86_64.lean`):

1. `scratch` to `r8`, and `d`'s pointer to `rcx` and `rdx` too, as the
   signature's arguments `k` and `digest`; then the signature's code up to
   `Z^(p-2)`, unchanged: its setup (which reads `d` into the slots of `k`,
   `d` and the hash), its tables of bits, `Q = [d]G` by its ladder, and its
   power;
2. `x = X Z^(p-2)` and `y = Y Z^(p-2)`, each left Montgomery's form by a
   multiplication by 1;
3. the flag, `d` in `[1, n-1]` and `Z ≠ 0`, as a mask, selects `04 ‖ x ‖ y`
   or zeros for `out` (big-endian), and is returned as 0 or 1.

`Z = 0` iff `Q = O`, which the flag rejects as the specification does
(it cannot happen for `d` in `[1, n-1]`, as `G` has the prime order `n`).
Everything is computed whatever the flag, and only the pointers may affect
timing.
-/

namespace VG.Impl.EcKey.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-! Slots of the signature's layout that the public key does not otherwise use. -/

/-- `Y Z^(p-2)`, in Montgomery form. -/
def YM : Nat := RM
/-- `y`. -/
def Y : Nat := SS

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `scratch` to `r8`, `d`'s pointer to `rcx` and `rdx`: the signature's
arguments, with `k` and the hash both `d`. -/
def args : List Instr := [.mov .r8 (.reg .rdx), .mov .rcx (.reg .rsi), .mov .rdx (.reg .rsi)]

/-- The signature's code up to `Z^(p-2)`. -/
def upToPow : Prog isa :=
  .seq (.block c.setup) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq (ladder c.ladderCfg) <|
  .seq (pow c.powP) (.block [])

/-- `04 ‖ x ‖ y` (or zeros) to `out`, the flag's low bit to `rax`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .rcx (.mem (sc (c.sl FLAG))), .mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx),
    .store8 { base := .r14, disp := 0 } .rax] ++
  storeBE c.n .r14 1 (c.sl X) ++ storeBE c.n .r14 (1 + 8 * c.n) (c.sl Y) ++
  [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] ++
  Impl.Ecdsa.X86_64.Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `x = X Z⁻¹` and `y = Y Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery
form, the checks of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  blocks [Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.X86_64.mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC),
    Mont.X86_64.mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE),
    c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c]

/-- `vg_ec_<curve>_public_key`. -/
def publicKey : Prog isa :=
  .seq (.block args) (.seq (upToPow c) (middle c))

end Cfg

end VG.Impl.EcKey.X86_64
