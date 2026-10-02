import VerifiedGarbage.Impl.Aes.Arm.Ctr32
import VerifiedGarbage.Impl.Aes.Arm.ExpandKey
import VerifiedGarbage.Impl.Gcm.Arm

/-!
# AES-GCM: 32-bit ARM implementation

The AES-GCM functions of `Spec/Gcm/Contract.lean`, composed of calls of the
verified `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash`.

`vg_aes_ctr32(schedule, rounds, counter, data, n, scratch)` takes `n` and
`scratch` on the stack, and `vg_ghash(h, y, data, n, scratch)` takes
`scratch` on the stack: a frame pushes them (`push {r12, lr}`: `n` in `r12`
and the working space in `lr` for `vg_aes_ctr32`, the working space in `r12`
for `vg_ghash`) around each call, and its pop loads `r12` back. So the
functions use 8 bytes of stack. Every other argument is read from where the
caller put it, the stack arguments with `ldr rX, [sp, #off]` whenever they
are needed (the stack pointer is the one on entry outside the frames).

## The working space

Every function has a buffer `W` of 2560 bytes (`scratch` or `work`):

* `[0, 16)`: the tag (written by `finish`, `verify` and `seal`; the received
  tag of `verify` and `open`);
* `[16, 96)`: the streaming state of `seal` and `open`;
* `[96, 112)`: a block `T`: a partial block padded with zeros, or the
  lengths block;
* `[112, 128)`: the tag `open` computes;
* `[128, 164)`: our caller's `r4`–`r11` and our return address `lr`;
* `[240, 256)` and `[256, 272)`: the two tags compared, padded with zeros;
* `[512, 2560)`: the working space of the functions called.

## Registers

`r11` holds `W`, `r10` the streaming state and `r9` the key context
throughout, and `r8` the number of rounds in the functions that need it; the
functions called preserve them (they are callee-saved). The pieces below
(`absorb`, `crypt`, …) take their arguments in `r4` (a pointer), `r5` (a
length) and `r6` (an offset), which the callees also preserve, and `lens`
the two 64-bit lengths in `r4:r5` and `r6:r7` (low words first). `r0`–`r3`,
`r12` and `lr` are temporaries.

## The pieces

* `absorb yo`: GHASH, with the accumulator at `r10 + yo` and the partial
  block at `r10 + 32` holding `r6` bytes, absorbs the `r5` bytes at `r4`:
  the partial block filled first (and absorbed if full), then whole blocks,
  then the last bytes buffered.
* `flush yo`: the `r6` buffered bytes padded with zeros, and absorbed.
* `lens yo`: the lengths block of `r5:r4` bytes of additional data and
  `r7:r6` bytes of text, absorbed.
* `crypt`: the `r5` bytes at `r4` XORed with the keystream, `r6` bytes into
  the current keystream block: the rest of that block (at `r10 + 64`), then
  whole blocks with `vg_aes_ctr32` from the counter block at `r10 + 48`,
  then a new keystream block for the last bytes.
* `tag o`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)` written to
  `W + o`, with `vg_aes_ctr32` on it with the counter block `J₀` (at `r10`).
* `j0`: `J₀` for the `r5`-byte nonce at `r4` (GHASH'd with `absorb`,
  `flush` and `lens` unless it is 12 bytes, its length kept in `r7`), and the
  state's accumulator and first counter block `inc₃₂(J₀)` (`initState`).
* `recv`, `cmp o`: the received tag and the computed one (at `W + o`), each
  of `r6` bytes, padded with zeros; `r0` is 1 if they are equal and 0 if
  not, without a branch (`1 - ((x | -x) >> 31)` of the OR `x` of the XORs
  of their words).

The model has no register-offset addressing and branches only on `Z`: the
bytes are copied and XORed through advancing pointers, counting down with
`subs`, and `min (16 - r6, r5)` takes the carry of a comparison with `adc`.
Only the pointers, the lengths, `rounds`, `tag_len` and (for `open`) whether
the tag is right can affect timing: the branches are on those, and the
comparison is masked.
-/

namespace VG.Impl.AesGcm.Arm

open VG.Arm

/-- `#n` as an operand. -/
def imm (n : Nat) : Op2 := .imm (BitVec.ofNat 32 n)

/-- `d := r + k`. -/
def addI (d r : Reg) (k : Nat) : Instr := .dp .add d r (imm k)

/-! ## The working space -/

def tO : Nat := 96
def uO : Nat := 112
def vO : Nat := 240
def rO : Nat := 256
def scrO : Nat := 512

/-- Our caller's registers, and where we save them. -/
def saved : List (Reg × Nat) :=
  [(.r4, 128), (.r5, 132), (.r6, 136), (.r7, 140), (.r8, 144), (.r9, 148), (.r10, 152), (.r11, 156),
   (.lr, 160)]

/-- Saves them at `b + 128`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str r b d

/-- The order of the restore: `r11` (which holds `W`) last. -/
def restored : List (Reg × Nat) :=
  [(.r4, 128), (.r5, 132), (.r6, 136), (.r7, 140), (.r8, 144), (.r9, 148), (.r10, 152), (.lr, 160),
   (.r11, 156)]

/-- Restores them, with `r11` holding `W`. -/
def restore : List Instr := restored.map fun (r, d) => .ldr r .r11 d

/-! ## The calls -/

/-- `vg_aes_ctr32`, with `n` in `r12` and the working space in `lr` pushed as
its stack arguments. -/
def ctrFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_ctr32" Impl.Aes.Arm.ctr32) (.pop .r12 8)

/-- `vg_ghash`, with the working space in `r12` pushed as its stack argument. -/
def ghFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_ghash" Impl.Gcm.Arm.ghash) (.pop .r12 8)

/-! ## Loops -/

/-- Copies the `r3` (at least 1) bytes at `r1` to `r2`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r1 0, .strb .r12 .r2 0, addI .r1 .r1 1, addI .r2 .r2 1,
    .subs .r3 .r3 (imm 1)]) .ne

/-- XORs the `r3` (at least 1) bytes at `r1` into those at `r2`, advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r2 0, .ldrb .r0 .r1 0, .dp .eor .r12 .r12 (.reg .r0), .strb .r12 .r2 0,
    addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]) .ne

/-- `r3 := min (16 - r6, r5)`: the carry of `r5 - (16 - r6)`, into `r12`, says
whether `16 - r6 ≤ r5`. -/
def minLen : Prog isa :=
  .seq (.block [.mov .r3 (imm 16), .dp .sub .r3 .r3 (.reg .r6), .cmp .r5 (.reg .r3), .mov .r12 (imm 0),
      .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)])
    (.ite .eq (.block [.mov .r3 (.reg .r5)]) (.block []))

/-! ## GHASH -/

/-- `vg_ghash` of the block at `b + o` into the accumulator at `r10 + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1), addI .r12 .r11 scrO])
    ghFrame

/-- Before the buffer is absorbed: the buffer filled from `r4` (`r3` bytes),
the arguments advanced, and `Z` set if the buffer is full. -/
def headPre : Prog isa :=
  .seq minLen
  (.seq (.block [addI .r2 .r10 32, .dp .add .r2 .r2 (.reg .r6), .mov .r1 (.reg .r4),
      .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3), .dp .add .r6 .r6 (.reg .r3)])
  (.seq copyLoop (.block [.cmp .r6 (imm 16)])))

/-- The buffer filled from `r4`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq headPre (.ite .eq (ghash1 yo .r10 32) (.block []))

/-- The whole blocks at `r4` split off: their address in `r2` and number in
`r3`, `r4` and `r5` the rest; `Z` set if there are none. -/
def splitWhole : List Instr :=
  [.mov .r2 (.reg .r4), .mov .r3 (.shifted .r5 .lsr 4), .dp .and .r12 .r5 (imm 15),
   .dp .sub .r0 .r5 (.reg .r12), .dp .add .r4 .r4 (.reg .r0), .mov .r5 (.reg .r12), .cmp .r3 (imm 0)]

/-- The whole blocks at `r4` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block splitWhole)
    (.ite .eq (.block [])
      (.seq (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO]) ghFrame))

/-- The last `r5` bytes at `r4` buffered. -/
def absorbTail : Prog isa :=
  .seq (.block [.cmp .r5 (imm 0)])
    (.ite .eq (.block []) (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r10 32, .mov .r3 (.reg .r5)]) copyLoop))

/-- The buffer filled first, if it holds bytes. -/
def absorbFill (yo : Nat) : Prog isa :=
  .seq (.block [.cmp .r6 (imm 0)]) (.ite .eq (.block []) (absorbHead yo))

def absorb (yo : Nat) : Prog isa :=
  .seq (.block [.cmp .r5 (imm 0)])
    (.ite .eq (.block []) (.seq (absorbFill yo) (.seq (absorbWhole yo) absorbTail)))

/-- `T` zeroed, and the arguments of the copy of the `r6` buffered bytes to it. -/
def flushPre : List Instr :=
  [.mov .r12 (imm 0), .str .r12 .r11 tO, .str .r12 .r11 (tO + 4), .str .r12 .r11 (tO + 8),
   .str .r12 .r11 (tO + 12), addI .r1 .r10 32, addI .r2 .r11 tO, .mov .r3 (.reg .r6)]

/-- The `r6` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .seq (.block [.cmp .r6 (imm 0)])
    (.ite .eq (.block []) (.seq (.seq (.block flushPre) copyLoop) (ghash1 yo .r11 tO)))

/-- `[8 (hi:lo)]₆₄`, big-endian, into `W + o`. -/
def be64Store (lo hi : Reg) (o : Nat) : List Instr :=
  [.mov .r0 (.shifted hi .lsl 3), .dp .orr .r0 .r0 (.shifted lo .lsr 29), .rev .r0 .r0, .str .r0 .r11 o,
   .mov .r0 (.shifted lo .lsl 3), .rev .r0 .r0, .str .r0 .r11 (o + 4)]

/-- The lengths block of `r5:r4` and `r7:r6` bytes, absorbed. -/
def lens (yo : Nat) : Prog isa :=
  .seq (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) (ghash1 yo .r11 tO)

/-! ## Counter mode -/

/-- The rest of the keystream block, from byte `r6`, into `r4`. -/
def cryptHead : Prog isa :=
  .seq minLen
  (.seq (.block [addI .r1 .r10 64, .dp .add .r1 .r1 (.reg .r6), .mov .r2 (.reg .r4),
      .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)])
    xorLoop)

/-- The whole blocks at `r4` split off: their address in `r3` and number in
`r12`, `r4` and `r5` the rest; `Z` set if there are none. -/
def splitCtr : List Instr :=
  [.mov .r3 (.reg .r4), .mov .r12 (.shifted .r5 .lsr 4), .dp .and .r0 .r5 (imm 15),
   .dp .sub .r1 .r5 (.reg .r0), .dp .add .r4 .r4 (.reg .r1), .mov .r5 (.reg .r0), .cmp .r12 (imm 0)]

/-- Whole blocks at `r4`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitCtr)
    (.ite .eq (.block [])
      (.seq (.block [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO])
        ctrFrame))

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` on it. -/
def tailArgs : List Instr :=
  [.mov .r12 (imm 0), .str .r12 .r10 64, .str .r12 .r10 68, .str .r12 .r10 72, .str .r12 .r10 76,
   .mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .r3 .r10 64, .mov .r12 (imm 1),
   addI .lr .r11 scrO]

/-- The last `r5` bytes at `r4`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block [.cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.seq (.block tailArgs) ctrFrame)
        (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop)))

/-- The rest of the keystream block first, if the text so far ends within a block. -/
def cryptFill : Prog isa :=
  .seq (.block [.cmp .r6 (imm 0)]) (.ite .eq (.block []) cryptHead)

def crypt : Prog isa :=
  .seq (.block [.cmp .r5 (imm 0)]) (.ite .eq (.block []) (.seq cryptFill (.seq cryptWhole cryptTail)))

/-! ## The tag and `J₀` -/

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32` on
it with the counter block `J₀`. -/
def tagArgs (o : Nat) : List Instr :=
  [.ldr .r0 .r10 16, .str .r0 .r11 o, .ldr .r0 .r10 20, .str .r0 .r11 (o + 4), .ldr .r0 .r10 24,
   .str .r0 .r11 (o + 8), .ldr .r0 .r10 28, .str .r0 .r11 (o + 12), .mov .r0 (.reg .r9),
   .mov .r1 (.reg .r8), .mov .r2 (.reg .r10), addI .r3 .r11 o, .mov .r12 (imm 1), addI .lr .r11 scrO]

/-- The tag into `W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens 16) (.seq (.block (tagArgs o)) ctrFrame)

/-- `J₀` of a 12-byte nonce: its three words and `0x00000001` (big-endian). -/
def j012 : List Instr :=
  [.ldr .r0 .r4 0, .ldr .r1 .r4 4, .ldr .r2 .r4 8, .mov .r3 (imm 0x01000000), .str .r0 .r10 0,
   .str .r1 .r10 4, .str .r2 .r10 8, .str .r3 .r10 12]

/-- `J₀` of any other nonce: GHASH of the nonce padded, then of the lengths
block of no additional data and the nonce, from a zero block at the state. -/
def j0hash : Prog isa :=
  .seq (.block [.mov .r0 (imm 0), .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12,
      .mov .r7 (.reg .r5), .mov .r6 (imm 0)])
  (.seq (absorb 0)
  (.seq (.block [.dp .and .r6 .r7 (imm 15)])
  (.seq (flush 0)
  (.seq (.block [.mov .r4 (imm 0), .mov .r5 (imm 0), .mov .r6 (.reg .r7), .mov .r7 (imm 0)])
    (lens 0)))))

/-- The first counter block `inc₃₂(J₀)`, word by word, and the accumulator zeroed. -/
def initState : List Instr :=
  [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
   .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60, .mov .r0 (imm 0),
   .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28]

/-- The streaming state for the `r5`-byte nonce at `r4`. -/
def j0 : Prog isa :=
  .seq (.block [.cmp .r5 (imm 12)]) (.seq (.ite .eq (.block j012) j0hash) (.block initState))

/-! ## Comparing tags -/

/-- `W + o` zeroed (16 bytes) with `r0`. -/
def zero16 (o : Nat) : List Instr :=
  [.mov .r0 (imm 0), .str .r0 .r11 o, .str .r0 .r11 (o + 4), .str .r0 .r11 (o + 8), .str .r0 .r11 (o + 12)]

/-- The `r6` bytes of the received tag (at `W`), padded with zeros at `W + rO`. -/
def recv : Prog isa :=
  .seq (.block (zero16 rO ++ [.mov .r1 (.reg .r11), addI .r2 .r11 rO, .mov .r3 (.reg .r6)])) copyLoop

/-- Word `k` of the XOR of the two padded tags into `d`. -/
def xorW (d : Reg) (k : Nat) : List Instr :=
  [.ldr d .r11 (vO + 4 * k), .ldr .r2 .r11 (rO + 4 * k), .dp .eor d d (.reg .r2)]

/-- `r0 = 1` if the padded tags are equal, else 0, without a branch. -/
def cmpTail : List Instr :=
  xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 2 ++
    [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
    [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
     .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
     .dp .sub .r0 .r1 (.reg .r0)]

/-- The first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + vO`, compared with the received one: `r0 = 1` if they are equal. -/
def cmp (o : Nat) : Prog isa :=
  .seq (.block (zero16 vO ++ [addI .r1 .r11 o, addI .r2 .r11 vO, .mov .r3 (.reg .r6)]))
    (.seq copyLoop (.block cmpTail))

/-- `r0 := 1` if `r6 = k`. -/
def chk (k : Nat) : Prog isa :=
  .seq (.block [.cmp .r6 (imm k)]) (.ite .eq (.block [.mov .r0 (imm 1)]) (.block []))

/-- `Z` is clear iff the tag length `r6` is one §5.2.1.2 allows (4, 8 or 12
to 16). -/
def tagLenOk : Prog isa :=
  .seq (.block [.mov .r0 (imm 0)])
  (.seq (chk 4) (.seq (chk 8) (.seq (chk 12) (.seq (chk 13) (.seq (chk 14) (.seq (chk 15)
  (.seq (chk 16) (.block [.cmp .r0 (imm 0)]))))))))

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`. -/
def initPre : List Instr :=
  save .r3 ++ [.mov .r11 (.reg .r3), .mov .r9 (.reg .r2), .mov .r8 (.shifted .r1 .lsr 2), addI .r8 .r8 6,
    addI .r3 .r11 scrO]

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
def initArgs : List Instr :=
  [.mov .r0 (imm 0), .str .r0 .r9 240, .str .r0 .r9 244, .str .r0 .r9 248, .str .r0 .r9 252,
   .str .r0 .r11 tO, .str .r0 .r11 (tO + 4), .str .r0 .r11 (tO + 8), .str .r0 .r11 (tO + 12),
   .mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r11 tO, addI .r3 .r9 240, .mov .r12 (imm 1),
   addI .lr .r11 scrO]

def init : Prog isa :=
  .seq (.block initPre)
  (.seq (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey)
  (.seq (.block initArgs) (.seq ctrFrame (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = r0, nonce = r1, nonce_len = r2, state = r3, scratch = [sp])`. -/
def streamInitPre : List Instr :=
  .ldrSp .r12 0 :: save .r12 ++
    [.mov .r11 (.reg .r12), .mov .r10 (.reg .r3), .mov .r9 (.reg .r0), .mov .r4 (.reg .r1), .mov .r5 (.reg .r2)]

def streamInit : Prog isa :=
  .seq (.block streamInitPre) (.seq j0 (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = r0, state = r1, aad_len = r2:r3, data = [sp], len = [sp + 4],
scratch = [sp + 8])`. -/
def streamAadPre : List Instr :=
  .ldrSp .r12 8 :: save .r12 ++
    [.mov .r11 (.reg .r12), .mov .r10 (.reg .r1), .mov .r9 (.reg .r0), .ldrSp .r4 0, .ldrSp .r5 4,
     .dp .and .r6 .r2 (imm 15)]

def streamAad : Prog isa :=
  .seq (.block streamAadPre) (.seq (absorb 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx = r0, rounds = r1, state = r2,
aad_len = [sp]:[sp + 4], text_len = [sp + 8]:[sp + 12], data = [sp + 16], len = [sp + 20],
scratch = [sp + 24])`. -/
def cryptEntry : List Instr :=
  .ldrSp .r12 24 :: save .r12 ++
    [.mov .r11 (.reg .r12), .mov .r10 (.reg .r2), .mov .r9 (.reg .r0), .mov .r8 (.reg .r1)]

/-- The arguments of `crypt` or `absorb` for the text: the data, its length,
and the length of the text so far modulo 16. -/
def textArgs : List Instr := [.ldrSp .r4 16, .ldrSp .r5 20, .ldrSp .r6 8, .dp .and .r6 .r6 (imm 15)]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa :=
  .seq (.block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)]) (flush 16)

/-- `Z` set iff `text_len` (`[sp + 8]:[sp + 12]`) is 0. -/
def tlenZero : List Instr := [.ldrSp .r0 8, .ldrSp .r1 12, .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (imm 0)]

/-- The text (`len` bytes at `data`) absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .seq (.block [.ldrSp .r5 20, .cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.block tlenZero)
      (.seq (.ite .eq firstFlush (.block []))
      (.seq (.block textArgs) (absorb 16)))))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish` and `verify`: `(ctx = r0, rounds = r1, state = r2,
aad_len = [sp]:[sp + 4], text_len = [sp + 8]:[sp + 12], work = [sp + 16])`. -/
def finEntry : List Instr :=
  .ldrSp .r12 16 :: save .r12 ++
    [.mov .r11 (.reg .r12), .mov .r10 (.reg .r2), .mov .r9 (.reg .r0), .mov .r8 (.reg .r1)]

/-- The buffered bytes padded and absorbed, and the tag into `W + o`. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.block tlenZero)
  (.seq (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8]))
  (.seq (.block [.dp .and .r6 .r6 (imm 15)])
  (.seq (flush 16)
  (.seq (.block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12])
    (tag o)))))

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag 0) (.block restore))

/-- The tag at `W` masked with `-r0`: kept if `r0 = 1`, zeroed if `r0 = 0`. -/
def mask : List Instr :=
  [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .ldr .r2 .r11 0, .dp .and .r2 .r2 (.reg .r1),
   .str .r2 .r11 0, .ldr .r2 .r11 4, .dp .and .r2 .r2 (.reg .r1), .str .r2 .r11 4, .ldr .r2 .r11 8,
   .dp .and .r2 .r2 (.reg .r1), .str .r2 .r11 8, .ldr .r2 .r11 12, .dp .and .r2 .r2 (.reg .r1),
   .str .r2 .r11 12]

/-- `vg_aes_gcm_stream_verify`, with `tag_len = [sp + 20]`. -/
def streamVerify : Prog isa :=
  .seq (.block (finEntry ++ [.ldrSp .r6 20]))
  (.seq tagLenOk
  (.seq (.ite .eq (.block (zero16 0))
      (.seq recv
      (.seq (finTag 0)
      (.seq (.block [.ldrSp .r6 20])
      (.seq (cmp 0) (.block mask))))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx = r0, rounds = r1, nonce = r2,
nonce_len = r3, aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
work = [sp + 16])`. The state is at `W + 16`. -/
def oneEntry : List Instr :=
  .ldrSp .r12 16 :: save .r12 ++
    [.mov .r11 (.reg .r12), addI .r10 .r11 16, .mov .r9 (.reg .r0), .mov .r8 (.reg .r1),
     .mov .r4 (.reg .r2), .mov .r5 (.reg .r3)]

/-- `J₀`, then the additional data absorbed and padded. -/
def oneAad : Prog isa :=
  .seq j0
  (.seq (.block [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)])
  (.seq (absorb 16)
  (.seq (.block [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)])
    (flush 16))))

/-- The arguments of `crypt` or `absorb` for the data, from its start. -/
def dataArgs : List Instr := [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r6 (imm 0)]

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block dataArgs)
  (.seq (absorb 16)
  (.seq (.block [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)])
  (.seq (flush 16)
  (.seq (.block [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12, .mov .r7 (imm 0)])
    (tag o)))))

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa := .seq (.block dataArgs) crypt

/-- `vg_aes_gcm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block oneEntry) (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.block restore))))

/-- `vg_aes_gcm_open`, with `tag_len = [sp + 20]`. -/
def «open» : Prog isa :=
  .seq (.block (oneEntry ++ [.ldrSp .r6 20]))
  (.seq tagLenOk
  (.seq (.ite .eq (.block [.mov .r0 (imm 0)])
      (.seq oneAad
      (.seq (oneTag uO)
      (.seq (.block [.ldrSp .r6 20])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)])
      (.seq (.ite .eq (.block []) oneCrypt)
        (.block [.mov .r0 (.reg .r7)])))))))))
    (.block restore)))

end VG.Impl.AesGcm.Arm
