import VerifiedGarbage.Impl.CmacAes.X86_64

/-!
# Streaming AES-CMAC: x86-64 implementation

`vg_cmac_aes_init(state = rdi, key = rsi, key_len = rdx, scratch = rcx)`,
`vg_cmac_aes_absorb(state = rdi, rounds = rsi, count = rdx, data = rcx, len = r8, scratch = r9)`
and `vg_cmac_aes_finish(state = rdi, rounds = rsi, count = rdx, out = rcx, scratch = r8)`
(see `VG.Spec.Cmac.aesInitContract` and the others), composed of calls of
the verified `vg_aes_expand_key`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update`
and `vg_cmac_aes_finalize`. Like those, they are generic over the
implementation of AES they call (`Ctr32`, the `ExpandKey` that goes with it,
and `sfx`, the suffix of the names of the CMAC functions made with it): e.g.
`vg_cmac_aes_absorb_aesni` calls `vg_cmac_aes_update_aesni`.

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer (2304 bytes): `[0, 2176)` is the working space of the functions
called, and `[2176, 2224)` our caller's callee-saved registers.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value, keeping the state (`rbx`), the scratch buffer
  (`rbp`) and the rounds (`r12`) across the calls.
* `absorb` keeps the state (`rbx`), the rounds (`rbp`), the data left
  (`r13`, `r14` bytes) and the scratch buffer (`r15`) across the calls.
  With `h` bytes held back (`count` modulo 16, but 16 for a multiple of 16
  and 0 for the empty message), it copies `f = min(len, 16 - h)` bytes
  after them. If data is left (the block held back is whole and not the
  last), it chains that block, then the whole blocks of what is left but
  its last 1 to 16 bytes, which it copies to the start of the bytes held
  back. With no data left, the two calls chain no blocks and the second
  copy copies nothing, so the code has no branch around a call.
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes.

Only the pointers, the key length, `count` and `len` can affect timing: the
branches are on them, and so are the number of bytes copied and of blocks
chained.
-/

namespace VG.Impl.CmacAes.Stream.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32 ExpandKey)
open VG.Impl.CmacAes.X86_64 (at_)

/-- Where our caller's callee-saved registers are kept in the scratch buffer. -/
def sOff : Nat := 2176

/-! ## `vg_cmac_aes_init` -/

def initSaved : List (Reg × Nat) := [(.rbx, sOff), (.rbp, sOff + 8), (.r12, sOff + 16)]

/-- Saves the registers, keeps the state in `rbx`, the scratch buffer in
`rbp` and the rounds (`key_len / 4 + 6`) in `r12`, and sets up the arguments
of `vg_aes_expand_key(key = rdi, key_len = rsi, schedule = rdx, scratch = rcx)`. -/
def initPre : List Instr :=
  initSaved.map (fun (r, d) => .store (at_ .rcx d) r) ++
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rcx), .mov .r12 (.reg .rdx), .shift .shr .r12 2,
   .alu .add .r12 (.imm 6), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rdx), .mov .rdx (.reg .rbx)]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = rdi, rounds = rsi, subkeys = rdx, scratch = rcx)`. -/
def initMid : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 240),
   .mov .rcx (.reg .rbp)]

/-- The chaining value zeroed, and the registers restored (`rbp` last). -/
def initPost : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .rbx 272) .rax, .store (at_ .rbx 280) .rax,
   .mov .rbx (.mem (at_ .rbp sOff)), .mov .r12 (.mem (at_ .rbp (sOff + 16))),
   .mov .rbp (.mem (at_ .rbp (sOff + 8)))]

def init (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block initPre)
    (.seq (.call e.name e.code)
      (.seq (.block initMid) (.seq (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c))
        (.block initPost))))

/-! ## Copying bytes -/

/-- `[r13 + r10]` and `[rdx + r10]`. -/
def srcByte : MemOp := { base := .r13, index := some .r10 }
def dstByte : MemOp := { base := .rdx, index := some .r10 }

/-- The loop's body: one byte from `[r13 + r10]` to `[rdx + r10]`. -/
def copyBody : List Instr :=
  [.movzx8 .rax srcByte, .store8 dstByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]

/-- The `rcx` bytes at `r13` (none if `rcx` is 0) copied to `rdx`. -/
def copy : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block []) (.loop (.block copyBody) .ne))

/-! ## `vg_cmac_aes_absorb` -/

def saved : List (Reg × Nat) :=
  [(.rbx, sOff), (.rbp, sOff + 8), (.r12, sOff + 16), (.r13, sOff + 24), (.r14, sOff + 32),
   (.r15, sOff + 40)]

/-- Saves the registers and keeps the arguments in them. -/
def save : List Instr :=
  saved.map (fun (r, d) => .store (at_ .r9 d) r) ++
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8),
   .mov .r15 (.reg .r9), .alu .test .rdx (.reg .rdx)]

/-- The number of bytes held back for `count` (`rdx`, ZF set if it is 0), in `rax`. -/
def held : Prog isa :=
  .ite .e (.block [.mov32 .rax (.imm 0)])
    (.block [.mov .rax (.reg .rdx), .alu .sub .rax (.imm 1), .alu .and .rax (.imm 15),
      .alu .add .rax (.imm 1)])

/-- `f = min(len, 16 - h)` in `rcx`, and the destination `state + 288 + h` in `rdx`. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 16), .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)])
    (.seq (.ite .b (.block [.mov .rcx (.reg .r14)]) (.block []))
      (.block [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 288), .alu .add .rdx (.reg .rax)]))

/-- The data advanced past the `f` bytes copied; one block to chain (`r8`)
if data is left, else none; and the other arguments of
`vg_cmac_aes_update(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8, scratch = r9)`
for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.alu .add .r13 (.reg .rcx), .mov32 .r8 (.imm 0), .alu .sub .r14 (.reg .rcx)])
    (.seq (.ite .e (.block []) (.block [.mov32 .r8 (.imm 1)]))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm 272), .mov .rcx (.reg .rbx), .alu .add .rcx (.imm 288),
        .mov .r9 (.reg .r15)]))

/-- `16 nb` in `r12` for the `nb` whole blocks of the data left but its last
1 to 16 bytes (none if no data is left), and the arguments of
`vg_cmac_aes_update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.mov32 .r12 (.imm 0), .alu .test .r14 (.reg .r14)])
    (.seq (.ite .e (.block [])
        (.block [.mov .r12 (.reg .r14), .alu .sub .r12 (.imm 1), .mov .rax (.reg .r12),
          .alu .and .rax (.imm 15), .alu .sub .r12 (.reg .rax)]))
      (.block [.mov .r8 (.reg .r12), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
        .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 272), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15)]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.alu .add .r13 (.reg .r12), .alu .sub .r14 (.reg .r12), .mov .rdx (.reg .rbx),
   .alu .add .rdx (.imm 288), .mov .rcx (.reg .r14)]

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb (c : Ctr32) (sfx : String) : Prog isa :=
  .seq absorbPre
    (.seq (.call ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86_64.update c))
      (.seq chain2 (.seq (.call ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86_64.update c)) absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- The chaining value copied to `out`, and the arguments of
`vg_cmac_aes_finalize(key = rdi, rounds = rsi, state = rdx, last = rcx, last_len = r8, scratch = r9)`
but `last_len`; ZF set if `count` is 0. -/
def finishPre : List Instr :=
  [.mov .rax (.mem (at_ .rdi 272)), .store (at_ .rcx 0) .rax, .mov .rax (.mem (at_ .rdi 280)),
   .store (at_ .rcx 8) .rax, .mov .r9 (.reg .r8), .mov .r8 (.reg .rdx), .mov .rdx (.reg .rcx),
   .mov .rcx (.reg .rdi), .alu .add .rcx (.imm 288), .alu .test .r8 (.reg .r8)]

/-- `last_len`: the number of bytes held back for `count` (in `r8`). -/
def lastLen : Prog isa :=
  .ite .e (.block [])
    (.block [.alu .sub .r8 (.imm 1), .alu .and .r8 (.imm 15), .alu .add .r8 (.imm 1)])

/-- Everything before the call. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

def finish (c : Ctr32) (sfx : String) : Prog isa :=
  .seq finPre (.call ("vg_cmac_aes_finalize" ++ sfx) (Impl.CmacAes.X86_64.finalize c))

end VG.Impl.CmacAes.Stream.X86_64
