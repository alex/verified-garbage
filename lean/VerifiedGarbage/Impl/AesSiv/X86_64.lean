import VerifiedGarbage.Impl.CmacAes.Stream.X86_64

/-!
# AES-SIV: x86-64 implementation

`vg_aes_siv_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`,
`vg_aes_siv_s2v_start(ctx = rdi, rounds = rsi, d = rdx, scratch = rcx)`,
`vg_aes_siv_s2v_ad(ctx = rdi, rounds = rsi, d = rdx, data = rcx, len = r8, scratch = r9)`,
`vg_aes_siv_seal(ctx = rdi, rounds = rsi, d = rdx, data = rcx, len = r8, work = r9)` and
`vg_aes_siv_open` with the same arguments (see `VG.Spec.Siv.initContract` and the
others), composed of calls of the verified `vg_aes_expand_key`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update`, `vg_cmac_aes_finalize` and
`vg_aes_ctr32`. Like those, they are generic over the implementation of AES
they call (`Ctr32`, the `ExpandKey` that goes with it, and `sfx`, the suffix
of the names of the CMAC functions made with it).

The key context (`VG.Spec.Siv.KeyRepr`) is `K1`'s schedule (bytes 0–239), its
CMAC subkeys (240–271) and `K2`'s schedule (272–511), so bytes 0–271 are
`vg_cmac_aes_finalize`'s `key`. The working space (`scratch` or `work`, 2560
bytes): `[0, 16)` the synthetic IV (`seal`, `open`), `[16, 32)` a zero
block, `[32, 64)` the last bytes of S2V's last string (`tail`), `[64, 80)`
the counter `Q + i`, `[80, 96)` a keystream block, `[96, 112)` the counter
block passed to `vg_aes_ctr32`, `[112, 128)` the IV `open` computes,
`[128, 144)` a CMAC state, `[144, 160)` `dbl(D)`, `[160, 208)` our caller's
callee-saved registers, `[208, 232)` the data, its length and the key
context, and `[256, 2432)` the working space of the functions called.

* `init` expands `K1` into the context, derives its subkeys after it and
  expands `K2` after them.
* `s2v_start` writes `AES-CMAC(K1, <zero>)` to `d` with `vg_cmac_aes_finalize`
  of the zero block from a zero state.
* `s2v_ad` computes `AES-CMAC(K1, S)` into the CMAC state with
  `vg_cmac_aes_update` over the whole blocks of `S` but its last 1 to 16
  bytes and `vg_cmac_aes_finalize` of those (`cmacOf`), then replaces `D`
  with `dbl(D)` XOR it.
* `seal` finishes S2V with the plaintext into the IV (`finish`), then
  encrypts the plaintext with CTR from the IV with two bits cleared (`ctr`):
  each block, `vg_aes_ctr32` on a zero block with the counter block `Q + i`
  gives the keystream, whose first `min(16, left)` bytes are XORed into the
  data, and the counter is incremented as a 128-bit big-endian integer.
* `open` decrypts with CTR from the IV it is given, finishes S2V with the
  plaintext into `[112, 128)`, compares the two IVs without a branch and
  ANDs every byte of the data with the mask of the result.

`finish`, for a string `P` of `L` bytes: if `L < 16`, the tail is
`pad(P) XOR dbl(D)` and its CMAC is that of one complete block; otherwise,
with `nb = ⌊(L − 1) / 16⌋` whole blocks before the last 1 to 16 bytes,
`k = max(nb, 1) − 1` and `j = min(nb, 1)`, the tail is the last
`L − 16 k` bytes of `P` with `D` XORed into its last 16 (`P xorend D`), and
the CMAC chains the `k` blocks of `P`, then the first `j` blocks of the
tail, and finalizes the rest of the tail.

Only the pointers, `rounds`, the key length and `len` can affect timing:
the branches are on them, and so are the numbers of calls, bytes copied
and blocks chained.
-/

namespace VG.Impl.AesSiv.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32 ExpandKey)
open VG.Impl.CmacAes.X86_64 (at_)

/-! ## The working space -/

/-- The offset of the working space of the functions called. -/
def csOff : Nat := 256
def zOff : Nat := 16
def tailOff : Nat := 32
def cntOff : Nat := 64
def ksOff : Nat := 80
def cbOff : Nat := 96
def tOff : Nat := 112
def stOff : Nat := 128
def dbOff : Nat := 144
def saveOff : Nat := 160
def dataOff : Nat := 208
def lenOff : Nat := 216
def ctxOff : Nat := 224

def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- The calls of the CMAC functions made with `c`. -/
def callUpdate (c : Ctr32) (sfx : String) : Prog isa :=
  .call ("vg_cmac_aes_update" ++ sfx) (Impl.CmacAes.X86_64.update c)

def callFinalize (c : Ctr32) (sfx : String) : Prog isa :=
  .call ("vg_cmac_aes_finalize" ++ sfx) (Impl.CmacAes.X86_64.finalize c)

/-- `mov [b + d], r` for each `(r, d)` of `l` (`VG.X86_64.Spill.saveCode`). -/
def saveCode (b : Reg) (l : List (Reg × Nat)) : List Instr :=
  l.map fun p => .store { base := b, disp := p.2 } p.1

/-- `mov r, [b + d]` for each `(r, d)` of `l` (`VG.X86_64.Spill.restoreCode`). -/
def restoreCode (b : Reg) (l : List (Reg × Nat)) : List Instr :=
  l.map fun p => .mov p.1 (.mem { base := b, disp := p.2 })

def saved : List (Reg × Nat) :=
  [(.rbx, saveOff), (.rbp, saveOff + 8), (.r12, saveOff + 16), (.r13, saveOff + 24),
   (.r14, saveOff + 32), (.r15, saveOff + 40)]

/-- Saves the registers in the working space at `w`. -/
def save (w : Reg) : List Instr := saveCode w saved

/-- Restores the registers, with `r15` (restored last) the working space. -/
def restore : List Instr := restoreCode .r15 saved

/-- The 16 bytes at `b + d` zeroed (`rax` zero). -/
def zero16 (b : Reg) (d : Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ b d) .rax, .store (at_ b (d + 8)) .rax]

/-! ## `vg_aes_siv_init` -/

def initSaved : List (Reg × Nat) :=
  [(.rbx, saveOff), (.rbp, saveOff + 8), (.r12, saveOff + 16), (.r13, saveOff + 24),
   (.r14, saveOff + 32)]

/-- `initSaved` with `r13`, the base, last. -/
def initRestored : List (Reg × Nat) :=
  [(.rbx, saveOff), (.rbp, saveOff + 8), (.r12, saveOff + 16), (.r14, saveOff + 32),
   (.r13, saveOff + 24)]

/-- Saves the registers and keeps the key in `rbx`, the half length
(`key_len / 2`) in `rbp`, the context in `r12`, the working space in `r13`
and the rounds (`key_len / 8 + 6`) in `r14`; then the arguments of
`vg_aes_expand_key(key = rdi, key_len = rsi, schedule = rdx, scratch = rcx)`
for `K1`. -/
def initPre : List Instr :=
  saveCode .rcx initSaved ++
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .shift .shr .rbp 1, .mov .r12 (.reg .rdx),
   .mov .r13 (.reg .rcx), .mov .r14 (.reg .rsi), .shift .shr .r14 3, .alu .add .r14 (imm 6),
   .mov .rsi (.reg .rbp), .alu .add .rcx (imm csOff)]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = rdi, rounds = rsi, subkeys = rdx, scratch = rcx)`. -/
def initMid₁ : List Instr :=
  [.mov .rdi (.reg .r12), .mov .rsi (.reg .r14), .mov .rdx (.reg .r12), .alu .add .rdx (imm 240),
   .mov .rcx (.reg .r13), .alu .add .rcx (imm csOff)]

/-- The arguments of `vg_aes_expand_key` for `K2`. -/
def initMid₂ : List Instr :=
  [.mov .rdi (.reg .rbx), .alu .add .rdi (.reg .rbp), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r12),
   .alu .add .rdx (imm 272), .mov .rcx (.reg .r13), .alu .add .rcx (imm csOff)]

/-- The registers restored, with `r13` (restored last) the working space. -/
def initPost : List Instr := restoreCode .r13 initRestored

def init (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block initPre)
    (.seq (.call e.name e.code)
      (.seq (.block initMid₁)
        (.seq (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c))
          (.seq (.block initMid₂) (.seq (.call e.name e.code) (.block initPost))))))

/-! ## `vg_aes_siv_s2v_start` -/

/-- The zero block at `scratch + 16`, `D` zeroed, and the arguments of
`vg_cmac_aes_finalize(key = rdi, rounds = rsi, state = rdx, last = rcx, last_len = r8, scratch = r9)`
for the zero block (the key and the rounds are ours). -/
def startPre : List Instr :=
  zero16 .rcx zOff ++ [.store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
    .mov .r9 (.reg .rcx), .alu .add .r9 (imm csOff), .alu .add .rcx (imm zOff), .mov32 .r8 (imm 16)]

def s2vStart (c : Ctr32) (sfx : String) : Prog isa := .seq (.block startPre) (callFinalize c sfx)

/-! ## The CMAC of a string -/

/-- With the key context in `rbx`, the rounds in `rbp`, the string at `r13`
(`r14` bytes) and the working space in `r15`: the CMAC state at
`r15 + st` zeroed, `16 nb` in `rcx` for the `nb` whole blocks before the
last 1 to 16 bytes (none for the empty string), and the arguments of
`vg_cmac_aes_update` for them. -/
def cmacPre (st : Nat) : Prog isa :=
  .seq (.block (zero16 .r15 st ++ [.mov32 .rcx (.imm 0), .alu .test .r14 (.reg .r14)]))
    (.seq (.ite .e (.block [])
        (.block [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx),
          .alu .and .rax (imm 15), .alu .sub .rcx (.reg .rax)]))
      (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .store (at_ .r15 dbOff) .rcx,
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm st),
        .mov .rcx (.reg .r13), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]))

/-- The arguments of `vg_cmac_aes_finalize` for the last bytes: `16 nb` back
from `r15 + 144`, where `cmacPre` stored it. -/
def cmacMid (st : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r15 dbOff)), .mov .rcx (.reg .r13), .alu .add .rcx (.reg .rax),
   .mov .r8 (.reg .r14), .alu .sub .r8 (.reg .rax), .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
   .mov .rdx (.reg .r15), .alu .add .rdx (imm st), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]

/-- `AES-CMAC(K1, S)` into the 16 bytes at `r15 + st`. -/
def cmacOf (c : Ctr32) (sfx : String) (st : Nat) : Prog isa :=
  .seq (cmacPre st) (.seq (callUpdate c sfx) (.seq (.block (cmacMid st)) (callFinalize c sfx)))

/-! ## `vg_aes_siv_s2v_ad` -/

/-- Saves the registers and keeps the arguments in them: the context in
`rbx`, the rounds in `rbp`, `d` in `r12`, the string in `r13` (`r14` bytes)
and the working space in `r15`. -/
def adPre : List Instr :=
  save .r9 ++ [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9)]

/-- `D = dbl(D) XOR` the CMAC state: `dbl` in place (with `rbx` holding `d`),
then the XOR; the registers restored. -/
def adPost : List Instr :=
  [.mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
  [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
   .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))),
   .store (at_ .r12 8) .rax] ++ restore

def s2vAd (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block adPre) (.seq (cmacOf c sfx stOff) (.block adPost))

/-! ## Finishing S2V -/

/-- The `rcx` bytes at `r13` copied to `rdx` (`Impl.CmacAes.Stream.X86_64.copy`). -/
def copy : Prog isa := Impl.CmacAes.Stream.X86_64.copy

/-- The short case, `L < 16`: the tail is `pad(P)`, then `dbl(D)` (computed at
`r15 + 144` with `rbx` holding the working space, the context saved at
`r15 + 224`) is XORed into it. -/
def shortTail : Prog isa :=
  .seq (.block (zero16 .r15 tailOff ++ [.mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff),
      .mov .rcx (.reg .r14)]))
    (.seq copy
      (.block ([.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] ++
        Impl.CmacAes.X86_64.dbl dbOff dbOff ++
        [.mov .rbx (.mem (at_ .r15 ctxOff)),
         .mov .rax (.mem (at_ .r15 tailOff)), .alu .xor .rax (.mem (at_ .r15 dbOff)),
         .store (at_ .r15 tailOff) .rax, .mov .rax (.mem (at_ .r15 (tailOff + 8))),
         .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))), .store (at_ .r15 (tailOff + 8)) .rax])))

/-- The long case, `L ≥ 16`: `16 k` in `rax`, saved at `r15 + 144`; the
last `L − 16 k` bytes copied to the tail (the string pointer advanced by
`16 k` for the copy and back after it); `D` XORed into the last 16 bytes
of the tail. -/
def longTail : Prog isa :=
  .seq (.block [.alu .cmp .r14 (imm 17)])
    (.seq (.ite .b (.block [.mov32 .rax (.imm 0)])
        (.block [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .shift .shr .rcx 4,
          .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx), .alu .add .rax (.reg .rax),
          .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)]))
      (.seq (.block [.store (at_ .r15 dbOff) .rax, .alu .add .r13 (.reg .rax), .mov .rcx (.reg .r14),
          .alu .sub .rcx (.reg .rax), .mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff)])
        (.seq copy
          (.block [.mov .rax (.mem (at_ .r15 dbOff)), .alu .sub .r13 (.reg .rax), .mov .rcx (.reg .r14),
            .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .r15),
            .mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
            .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
            .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax]))))

/-- The long case's calls: `vg_cmac_aes_update` over the `k` blocks of `P`,
then over the first `j` blocks of the tail (`j` is 1 if `L > 16`, else 0),
then `vg_cmac_aes_finalize` of the rest of the tail, into `r15 + out`. -/
def longMac (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block (zero16 .r15 out ++
      [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
       .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
       .alu .add .r9 (imm csOff)]))
    (.seq (callUpdate c sfx)
      (.seq (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)])
        (.seq (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)]))
          (.seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
              .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
              .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8])
            (.seq (callUpdate c sfx)
              (.seq (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
                  .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
                  .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
                  .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
                  .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
                  .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)])
                (callFinalize c sfx)))))))

/-- The short case's call: `vg_cmac_aes_finalize` of the tail, one complete
block, from a zero state at `r15 + out`. -/
def shortMac (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block (zero16 .r15 out ++
      [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
       .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
       .alu .add .r9 (imm csOff)]))
    (callFinalize c sfx)

/-- S2V finished with the string at `r13` (`r14` bytes) from `D` at `r12`,
into the 16 bytes at `r15 + out`. -/
def finish (c : Ctr32) (sfx : String) (out : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .r14 (imm 16)])
    (.ite .b (.seq shortTail (shortMac c sfx out)) (.seq longTail (longMac c sfx out)))

/-! ## CTR -/

/-- The counter `Q`: the IV at `r15 + src` with bit 7 of its bytes 8 and 12
cleared, at `r15 + 64`. -/
def counter (src : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .r15 src)), .store (at_ .r15 cntOff) .rax, .mov .rax (.mem (at_ .r15 (src + 8))),
   .movImm64 .rdx 0xffffff7fffffff7f, .alu .and .rax (.reg .rdx), .store (at_ .r15 (cntOff + 8)) .rax]

/-- `[r13 + r10]` and `[r15 + r10 + 80]`. -/
def dataByte : MemOp := { base := .r13, index := some .r10 }
def ksByte : MemOp := { base := .r15, index := some .r10, disp := ksOff }

/-- The first `rcx` bytes of the keystream block (`rcx` from 1 to 16) XORed
into the data at `r13`. -/
def xorBytes : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0)])
    (.loop (.block [.movzx8 .rax dataByte, .movzx8 .rdx ksByte, .alu .xor .rax (.reg .rdx),
      .store8 dataByte .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne)

/-- The keystream block zeroed, the counter block `Q + i` passed to
`vg_aes_ctr32`, and its arguments: `K2`'s schedule, the rounds, the counter
block, the keystream block, one block and the working space. -/
def ctrPre : List Instr :=
  zero16 .r15 ksOff ++
  [.mov .rax (.mem (at_ .r15 cntOff)), .store (at_ .r15 cbOff) .rax,
   .mov .rax (.mem (at_ .r15 (cntOff + 8))), .store (at_ .r15 (cbOff + 8)) .rax,
   .mov .rdi (.reg .rbx), .alu .add .rdi (imm 272), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
   .alu .add .rdx (imm cbOff), .mov .rcx (.reg .r15), .alu .add .rcx (imm ksOff), .mov32 .r8 (imm 1),
   .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)]

/-- `min(16, left)` in `rcx`. -/
def ctrMin : Prog isa :=
  .seq (.block [.mov32 .rcx (imm 16), .alu .cmp .r14 (.reg .rcx)])
    (.ite .b (.block [.mov .rcx (.reg .r14)]) (.block []))

/-- The counter incremented as a 128-bit big-endian integer; the data
advanced past the block (ZF set when no data is left). -/
def ctrPost : List Instr :=
  [.mov .rax (.mem (at_ .r15 (cntOff + 8))), .bswap .rax, .mov .rdx (.mem (at_ .r15 cntOff)), .bswap .rdx,
   .alu .add .rax (imm 1), .alu .adc .rdx (imm 0), .bswap .rax, .bswap .rdx,
   .store (at_ .r15 cntOff) .rdx, .store (at_ .r15 (cntOff + 8)) .rax,
   .alu .add .r13 (imm 16), .alu .sub .r14 (.reg .rcx)]

/-- One block of CTR. -/
def ctrBody (c : Ctr32) : Prog isa :=
  .seq (.block ctrPre) (.seq (.call c.name c.code) (.seq ctrMin (.seq xorBytes (.block ctrPost))))

/-- The data at `r13` (`r14` bytes) XORed with the keystream of CTR under
`K2` from the counter at `r15 + 64`; `r13` and `r14` then back from
`r15 + 208` and `r15 + 216`. -/
def ctr (c : Ctr32) : Prog isa :=
  .seq (.block [.alu .test .r14 (.reg .r14)])
    (.seq (.ite .e (.block []) (.loop (ctrBody c) .ne))
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]))

/-! ## `vg_aes_siv_seal` and `vg_aes_siv_open` -/

/-- Saves the registers and keeps the arguments in them, the data and its
length also at `r15 + 208` and `r15 + 216`. -/
def cryptPre : List Instr :=
  adPre ++ [.store (at_ .r15 dataOff) .r13, .store (at_ .r15 lenOff) .r14]

def «seal» (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block cryptPre)
    (.seq (finish c sfx 0) (.seq (.block (counter 0)) (.seq (ctr c) (.block restore))))

/-- `rax = 1` if the IVs at `r15` and `r15 + 112` are equal, else 0
(`(¬a ∧ (a − 1)) >> 63` for `a` the OR of the XORs of their halves), saved at
`r15 + 144`, and the mask `0 − rax` in `r11`. -/
def compare : List Instr :=
  [.mov .rax (.mem (at_ .r15 0)), .alu .xor .rax (.mem (at_ .r15 tOff)), .mov .rdx (.mem (at_ .r15 8)),
   .alu .xor .rdx (.mem (at_ .r15 (tOff + 8))), .alu .or .rax (.reg .rdx), .mov .rdx (.reg .rax),
   .alu .sub .rdx (imm 1), .mov .rcx (.reg .rax), .alu .xor .rcx (.imm 0xffffffff),
   .alu .and .rcx (.reg .rdx), .mov .rax (.reg .rcx),
   .shift .shr .rax 63, .mov32 .r11 (.imm 0), .alu .sub .r11 (.reg .rax), .store (at_ .r15 dbOff) .rax]

/-- `[r13 + r10]`. -/
def maskByte : MemOp := { base := .r13, index := some .r10 }

/-- Every byte of the data (`r14` of them) ANDed with the mask in `r11`. -/
def maskData : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0), .alu .test .r14 (.reg .r14)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .r14)]) .ne))

def «open» (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block (cryptPre ++ counter 0))
    (.seq (ctr c)
      (.seq (finish c sfx tOff)
        (.seq (.block compare)
          (.seq maskData (.block ([.mov .rax (.mem (at_ .r15 dbOff))] ++ restore))))))

end VG.Impl.AesSiv.X86_64
