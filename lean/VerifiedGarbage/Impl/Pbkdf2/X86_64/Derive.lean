import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# PBKDF2-HMAC-SHA-256: x86-64 implementation

`derive(password = rdi, password_len = rsi, salt = rdx, salt_len = rcx,
c = r8d, out = r9, out_len = [rsp + 8], scratch = [rsp + 16])` writes
`PBKDF2-HMAC-SHA256 (P, S, c, out_len)` to `out` (`VG.Spec.Pbkdf2.pbkdf2`),
composed of calls of the verified SHA-256, HMAC-SHA-256 and PBKDF2
functions. It is defined for any implementation `f` of the compression
function: `derive f sfx` calls the functions made with `f`, whose names end
with `sfx` (e.g. `vg_sha256_update_shani`), and is emitted once for each
(`Generic/Sha256Compress/X86_64/Pbkdf2.lean`):

1. A password longer than a block (64 bytes) is hashed first
   (`vg_sha256_init`, `vg_sha256_update`, `vg_sha256_finalize`), which gives
   the same HMAC key `K₀` (RFC 2104 §2).
2. `vg_hmac_sha256_init` sets up the streaming states of `K₀ ⊕ ipad` and
   `K₀ ⊕ opad`, and `vg_sha256_update` absorbs the salt into a copy of the
   inner one.
3. For each block `i = 1, 2, …` of the derived key: a copy of that state
   absorbs `INT (i)` (`vg_sha256_update`), `vg_hmac_sha256_finalize` gives
   `U₁`, `vg_pbkdf2_hmac_sha256_iterate` exclusive-ors `U₂, …, U_c` into
   `T = U₁`, and the first `min (32, bytes left)` bytes of `T` are copied
   to `out`.

`scratch` (2048 bytes) holds:

* `[0, 192)`: the key's inner and outer streaming states (as
  `vg_pbkdf2_hmac_sha256_iterate` takes them);
* `[192, 288)`: the inner state after the salt;
* `[288, 384)`: the state being worked on (the password's hash, then each
  block's inner state);
* `[384, 416)`: `T`; `[416, 420)`: `INT (i)`;
* `[424, 472)`: our caller's `rbx, rbp, r12, r13, r14, r15`; `[472, 476)`:
  `c`;
* `[480, 512)`: the password's hash;
* `[512, 896)`: the working space of the functions we call but
  `vg_hmac_sha256_finalize`, whose working space is `[896, 1136)` (so the MAC
  it leaves in `[1072, 1104)` is `U₁`).

The functions we call preserve `rbx, rbp, r12–r15`: `rbx` is `scratch`
throughout. While the key is set up, `r12` and `r13` are the key and its
length, `r14` and `r15` the salt and its length, and `rbp` is `out`. In the
loop over the blocks, `rbp` is where the next block goes in `out`, `r12` is
`i`, `r13` the number of bytes left, `r14` is `c - 1` and `r15` is
`64 + salt_len`, the length of what the salted state represents.

Every branch and address depends only on the pointers, the lengths and `c`.
-/

namespace VG.Impl.Pbkdf2.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Impl.Hmac.X86_64 (cp64)

/-- `r + k` into `d`. -/
def ptr (d r : Reg) (k : Nat) : List Instr := [.mov d (.reg r), .alu .add d (.imm (BitVec.ofNat 32 k))]

/-- The callee-saved registers we use, and where they are saved in `scratch`.
`rbx` is last: the epilogue reads the others through it. -/
def dSaved : List (Reg × Nat) :=
  [(.rbp, 432), (.r12, 440), (.r13, 448), (.r14, 456), (.r15, 464), (.rbx, 424)]

/-- Saving our caller's registers, and setting up ours. -/
def dPrologue : List Instr :=
  [.mov .rax (.mem (at_ .rsp 16))] ++ dSaved.map (fun (r, d) => .store (at_ .rax d) r) ++
    [.mov .rbx (.reg .rax), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi), .mov .r14 (.reg .rdx),
      .mov .r15 (.reg .rcx), .mov .rbp (.reg .r9), .store32 (at_ .rbx 472) .r8,
      .alu .cmp .r13 (.imm 65)]

/-- A password longer than 64 bytes replaced by its hash: `r12 = scratch + 480`, `r13 = 32`. -/
def hashKey (f : Callee) (sfx : String) : Prog isa :=
  .seq (.block (ptr .rdi .rbx 288)) <|
  .seq (.call "vg_sha256_init" Impl.Sha256.X86_64.Stream.init) <|
  .seq (.block (ptr .rdi .rbx 288 ++ [.mov32 .rsi (.imm 0), .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)] ++
    ptr .r8 .rbx 512)) <|
  .seq (.call ("vg_sha256_update" ++ sfx) (Impl.Sha256.X86_64.Stream.update f)) <|
  .seq (.block (ptr .rdi .rbx 288 ++ [.mov .rsi (.reg .r13)] ++ ptr .rdx .rbx 480 ++ ptr .rcx .rbx 512)) <|
  .seq (.call ("vg_sha256_finalize" ++ sfx) (Impl.Sha256.X86_64.Stream.finalize f))
    (.block (ptr .r12 .rbx 480 ++ [.mov32 .r13 (.imm 32)]))

/-- The key's streaming states, and the salt absorbed into a copy of the inner one. -/
def keySalt (f : Callee) (sfx : String) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbx)] ++ ptr .rsi .rbx 96 ++ [.mov .rdx (.reg .r12), .mov .rcx (.reg .r13)] ++
    ptr .r8 .rbx 512)) <|
  .seq (.call ("vg_hmac_sha256_init" ++ sfx) (Impl.Hmac.X86_64.init f)) <|
  .seq (.block ((List.range 12).flatMap (cp64 .rbx .rbx 0 192) ++ ptr .rdi .rbx 192 ++
    [.mov32 .rsi (.imm 64), .mov .rdx (.reg .r14), .mov .rcx (.reg .r15)] ++ ptr .r8 .rbx 512))
    (.call ("vg_sha256_update" ++ sfx) (Impl.Sha256.X86_64.Stream.update f))

/-- The registers for the loop over the blocks; ZF is set if there are none. -/
def loopSetup : List Instr :=
  [.alu .add .r15 (.imm 64), .mov32 .r14 (.mem (at_ .rbx 472)), .alu .sub .r14 (.imm 1),
    .mov32 .r12 (.imm 1), .mov .r13 (.mem (at_ .rsp 8)), .alu .test .r13 (.reg .r13)]

/-- `U₁ = HMAC (P, S ‖ INT (i))`, left in `scratch[1072, 1104)`. -/
def blockU (f : Callee) (sfx : String) : Prog isa :=
  .seq (.block ((List.range 12).flatMap (cp64 .rbx .rbx 192 288) ++
    [.mov32 .rax (.reg .r12), .bswap32 .rax, .store32 (at_ .rbx 416) .rax] ++ ptr .rdi .rbx 288 ++
    [.mov .rsi (.reg .r15)] ++ ptr .rdx .rbx 416 ++ [.mov32 .rcx (.imm 4)] ++ ptr .r8 .rbx 512)) <|
  .seq (.call ("vg_sha256_update" ++ sfx) (Impl.Sha256.X86_64.Stream.update f)) <|
  .seq (.block (ptr .rdi .rbx 288 ++ ptr .rsi .rbx 96 ++ ptr .rdx .r15 4 ++ ptr .rcx .rbx 896))
    (.call ("vg_hmac_sha256_finalize" ++ sfx) (Impl.Hmac.X86_64.finalize f ("vg_sha256_finalize" ++ sfx)))

/-- `T = U₁ ⊕ U₂ ⊕ … ⊕ U_c` in `scratch[384, 416)`. -/
def blockT (f : Callee) (sfx : String) : Prog isa :=
  .seq (.block ((List.range 4).flatMap (cp64 .rbx .rbx 1072 384) ++ [.mov .rdi (.reg .rbx)] ++
    ptr .rsi .rbx 1072 ++ [.mov32 .rdx (.reg .r14)] ++ ptr .rcx .rbx 384 ++ ptr .r8 .rbx 512))
    (.call ("vg_pbkdf2_hmac_sha256_iterate" ++ sfx) (iterate f))

/-- The bytes `[rdi] → [rsi]`, `rcx > 0` of them. -/
def byteLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (at_ .rdi 0), .store8 (at_ .rsi 0) .rax, .alu .add .rdi (.imm 1),
    .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne

/-- The first `min (32, r13)` bytes of `T` to `rbp`; ZF is set if no bytes are left. -/
def blockOut : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 32), .alu .cmp .r13 (.imm 32)]) <|
  .seq (.ite .b (.block [.mov .rcx (.reg .r13)]) (.block [])) <|
  .seq (.block ([.alu .sub .r13 (.reg .rcx)] ++ ptr .rdi .rbx 384 ++ [.mov .rsi (.reg .rbp)])) <|
  .seq byteLoop
    (.block [.mov .rbp (.reg .rsi), .alu .add .r12 (.imm 1), .alu .test .r13 (.reg .r13)])

/-- One block of the derived key. -/
def block (f : Callee) (sfx : String) : Prog isa := .seq (blockU f sfx) (.seq (blockT f sfx) blockOut)

/-- Restoring our caller's registers. -/
def dEpilogue : List Instr := dSaved.map fun (r, d) => .mov r (.mem (at_ .rbx d))

def derive (f : Callee) (sfx : String) : Prog isa :=
  .seq (.block dPrologue) <|
  .seq (.ite .b (.block []) (hashKey f sfx)) <|
  .seq (keySalt f sfx) <|
  .seq (.block loopSetup) <|
  .seq (.ite .e (.block []) (.loop (block f sfx) .ne))
    (.block dEpilogue)

end VG.Impl.Pbkdf2.X86_64
