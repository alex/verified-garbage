import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# Ed448 public-key derivation on x86-64

`publicKey (out = rdi, seed = rsi, scratch = rdx)` computes
`SHAKE256(seed, 114)` with the sponge functions (`vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze`, rate 136), prunes the first 57
bytes of the hash (RFC 8032 §5.2.5) and encodes `[s]B` with
`vg_ed448_scalar_base`.

Everything runs in one stack frame of eleven words, pushed from `rdi`,
`rsi`, `rdx` and eight copies of `rax`: from `rsp`, the pruned scalar (eight
words, the last 0), then `scratch`, `seed` and `out`, which the calls cannot
change. The pruned scalar must lie outside `scratch` and `out`, which
`vg_ed448_scalar_base` writes; it is cleared before the frame is popped. In
`scratch`: the Keccak state (200 bytes), the sponge functions' working space
(640 bytes, at 256) and the hash (114 bytes, at 1024).
-/

namespace VG.Impl.Ed448.X86_64

open VG.X86_64

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- Where in the frame `scratch`, `seed` and `out` are. -/
def fScratch : Nat := 64
def fSeed : Nat := 72
def fOut : Nat := 80

/-- Where in `scratch` the sponge functions' working space and the hash are. -/
def keccakScratch : Nat := 256
def hashAt : Nat := 1024

/-- `d ← scratch + o`. -/
def scrPtr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `rdi = scratch`, `rax = 0`. -/
def pkZeroHead : List Instr := [.mov .rdi (.mem (stk fScratch)), .mov32 .rax (.imm 0)]

/-- The 25 words of the Keccak state at `rdi`, zeroed. -/
def pkZeroStores : List Instr :=
  (List.range 25).map fun k => .store { base := .rdi, disp := ((8 * k : Nat) : Int) } .rax

/-- The Keccak state at `scratch`, zeroed (the address, then the stores, in
blocks of their own: the stores' address is a pointer read from the frame). -/
def pkZeroState : Prog isa := .seq (.block pkZeroHead) (.block pkZeroStores)

/-- `absorb(state = scratch, rate = 136, pos = 0, data = seed, len = 57, scratch + 256)`. -/
def pkAbsorbArgs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 136), .mov32 .rdx (.imm 0),
    .mov .rcx (.mem (stk fSeed)), .mov32 .r8 (.imm 57)] ++ scrPtr .r9 keccakScratch

/-- `pad(state = scratch, rate = 136, pos = 57, suffix = 0x1f, scratch + 256)`. -/
def pkPadArgs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 136), .mov32 .rdx (.imm 57),
    .mov32 .rcx (.imm 0x1f)] ++ scrPtr .r8 keccakScratch

/-- `squeeze(state = scratch, rate = 136, pos = 0, out = scratch + 1024, len = 114, scratch + 256)`. -/
def pkSqueezeArgs : List Instr :=
  [.mov .rdi (.mem (stk fScratch)), .mov32 .rsi (.imm 136), .mov32 .rdx (.imm 0)] ++
    scrPtr .rcx hashAt ++ [.mov32 .r8 (.imm 114)] ++ scrPtr .r9 keccakScratch

/-- `scalar_base(out, scalar = rsp, scratch)`. -/
def pkBaseArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.reg .rsp), .mov .rdx (.mem (stk fScratch))]

/-- `[rdx + 1024 + 8 k]`: word `k` of the hash, with `scratch` in `rdx`. -/
def hashWord (k : Nat) : MemOp := { base := .rdx, disp := ((hashAt + 8 * k : Nat) : Int) }

/-- The registers that hold the words of the scalar on their way to the frame. -/
def pkRegs : List Reg := [.r8, .r9, .r10, .r11, .rax, .rcx, .rsi, .rdi]

/-- The first seven words of the hash into `r8`–`r11`, `rax`, `rcx` and `rsi`. -/
def pkLoads : List Instr :=
  [.mov .r8 (.mem (hashWord 0)), .mov .r9 (.mem (hashWord 1)),
    .mov .r10 (.mem (hashWord 2)), .mov .r11 (.mem (hashWord 3)), .mov .rax (.mem (hashWord 4)),
    .mov .rcx (.mem (hashWord 5)), .mov .rsi (.mem (hashWord 6))]

/-- Pruning (`Spec.Ed448.prune`): bits 0–1 cleared, bit 447 (the top of word
6) set, and the eighth word, whose low byte is the 57th, 0 in `rdi`. -/
def pkMods : List Instr :=
  [.alu .and .r8 (.imm (BitVec.ofInt 32 (-4))), .movImm64 .rdi (BitVec.ofNat 64 (2 ^ 63)),
    .alu .or .rsi (.reg .rdi), .mov32 .rdi (.imm 0)]

/-- The eight registers into the frame. -/
def pkStores : List Instr := (List.range 8).map fun k => .store (stk (8 * k)) (pkRegs.getD k .r8)

/-- The first 57 bytes of the hash at `scratch + 1024`, pruned, into the frame
(`rdx = scratch` in a block of its own: it is a pointer read from the frame). -/
def pkPrune : Prog isa :=
  .seq (.block [.mov .rdx (.mem (stk fScratch))]) (.block (pkLoads ++ (pkMods ++ pkStores)))

/-- The scalar in the frame, cleared. -/
def pkWipe : List Instr := (pkRegs.map fun r => .mov32 r (.imm 0)) ++ pkStores

/-- The moves of a call's arguments, and the call. -/
def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

/-- `SHAKE256(seed, 114)`, into `scratch + 1024`. -/
def pkHash : Prog isa :=
  .seq pkZeroState <|
  .seq (callWith pkAbsorbArgs "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) <|
  .seq (callWith pkPadArgs "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad)
    (callWith pkSqueezeArgs "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze)

/-- The frame's body. -/
def pkBody : Prog isa :=
  .seq pkHash <| .seq pkPrune <| .seq (.block pkBaseArgs) <|
    .seq (.call "vg_ed448_scalar_base" scalarBase) (.block pkWipe)

/-- `vg_ed448_public_key`. -/
def publicKey : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax]) pkBody (.pop .rax 11)

end VG.Impl.Ed448.X86_64
