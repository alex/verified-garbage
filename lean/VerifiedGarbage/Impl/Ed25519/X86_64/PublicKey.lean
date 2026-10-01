import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Impl.Sha512.X86_64.Stream
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Ed25519 public-key derivation on x86-64

`publicKey f suffix (out = rdi, seed = rsi, scratch = rdx)` computes
`SHA-512(seed)` with the streaming SHA-512 functions (`vg_sha512_init`, and
`update` and `finalize` made with the compression function `f`, named with
`suffix`), prunes the first half of the digest (RFC 8032 §5.1.5) and encodes
`[s]B` with `vg_ed25519_scalar_base_precomputed`.

Everything runs in one stack frame of seven words, pushed from `rdi`, `rsi`,
`rdx` and four copies of `rax`: from `rsp`, the pruned scalar (32 bytes),
then `scratch`, `seed` and `out`, which the calls cannot change. The
pruned scalar must lie outside `scratch` and `out`, which
`vg_ed25519_scalar_base_precomputed` writes; it is cleared before the frame
is popped. In `scratch`: the SHA-512 streaming state (192 bytes), the
working space of `update` and `finalize` (1376 bytes), and the digest (64
bytes, at 1568).
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.Sha512.X86_64.Stream (Callee)

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- Where in the frame `scratch`, `seed` and `out` are. -/
def fScratch : Nat := 32
def fSeed : Nat := 40
def fOut : Nat := 48

/-- Where in `scratch` the SHA-512 working space and the digest are. -/
def shaScratch : Nat := 192
def digestAt : Nat := 1568

/-- `d ← scratch + o`. -/
def scrPtr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `init(state = scratch)`. -/
def pkInitArgs : List Instr := [.mov .rdi (.mem (stk fScratch))]

/-- `update(state = scratch, count = 0, data = seed, len = 32, scratch + 192)`. -/
def pkUpdateArgs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 0), .mov .rdx (.mem (stk fSeed)),
    .mov32 .rcx (.imm 32)] ++ scrPtr .r8 shaScratch

/-- `finalize(state = scratch, count = 32, out = scratch + 1568, scratch + 192)`. -/
def pkFinalizeArgs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 32)] ++ scrPtr .rdx digestAt ++
    scrPtr .rcx shaScratch

/-- `scalar_base_precomputed(out, scalar = rsp, scratch)`. -/
def pkBaseArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.reg .rsp), .mov .rdx (.mem (stk fScratch))]

/-- `[rdx + 1568 + 8 k]`: word `k` of the digest, with `scratch` in `rdx`. -/
def digestWord (k : Nat) : MemOp := { base := .rdx, disp := ((digestAt + 8 * k : Nat) : Int) }

/-- The first half of the digest at `rdx + 1568`, pruned (`Spec.Ed25519.prune`),
in `r8`–`r11`: bits 0–2 and 255 cleared, bit 254 set. -/
def pkPruneRegs : List Instr :=
  [.mov .r8 (.mem (digestWord 0)), .mov .r9 (.mem (digestWord 1)),
    .mov .r10 (.mem (digestWord 2)), .mov .r11 (.mem (digestWord 3)),
    .alu .and .r8 (.imm (BitVec.ofInt 32 (-8))),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62 - 1)), .alu .and .r11 (.reg .rcx),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62)), .alu .or .r11 (.reg .rcx)]

/-- `r8`–`r11` into the frame. -/
def pkPruneStores : List Instr :=
  [.store (stk 0) .r8, .store (stk 8) .r9, .store (stk 16) .r10, .store (stk 24) .r11]

/-- The pruned first half of the digest, into the frame. -/
def pkPrune : List Instr := pkPruneRegs ++ pkPruneStores

/-- `r8`–`r11` cleared. -/
def pkZero : List Instr :=
  [.alu32 .xor .r8 (.reg .r8), .alu32 .xor .r9 (.reg .r9), .alu32 .xor .r10 (.reg .r10),
    .alu32 .xor .r11 (.reg .r11)]

/-- The scalar in the frame, cleared. -/
def pkWipe : List Instr := pkZero ++ pkPruneStores

/-- The moves of a call's arguments, and the call. -/
def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

/-- The hash of the seed, into `scratch + 1568`. -/
def pkHash (f : Callee) (suffix : String) : Prog isa :=
  .seq (callWith pkInitArgs Spec.Sha512.init512Api.name (Sha512.X86_64.Stream.init Spec.Sha512.H0_512))
    (.seq (callWith pkUpdateArgs (Spec.Sha512.updateApi.name ++ suffix) (Sha512.X86_64.Stream.update f))
      (callWith pkFinalizeArgs (Spec.Sha512.finalizeApi.name ++ suffix) (Sha512.X86_64.Stream.finalize f)))

/-- The name of the base-point multiplication called. -/
def scalarBaseName : String := "vg_ed25519_scalar_base_precomputed"

/-- The frame's body. -/
def pkBody (f : Callee) (suffix : String) : Prog isa :=
  .seq (pkHash f suffix)
    (.seq (.block pkBaseArgs) (.seq (.block pkPrune)
    (.seq (.call scalarBaseName scalarBase_precomputed) (.block pkWipe))))

/-- `vg_ed25519_public_key` (with `suffix`). -/
def publicKey (f : Callee) (suffix : String) : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax]) (pkBody f suffix) (.pop .rax 7)

end VG.Impl.Ed25519.X86_64
