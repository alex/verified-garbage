import VerifiedGarbage.Impl.Blake2.X86.CompressS

/-!
# Streaming BLAKE2: x86 (32-bit) implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`: the hash
value (`N = 8 · w/8` bytes, stored as `N / 4` little-endian 32-bit words)
followed by a `B`-byte buffer (`B = 16 · w/8`) holding the last block of the
data so far, 1 to `B` bytes of it (none for empty data). The caller keeps the
byte count, `count`, from which the number of buffered bytes follows. Every
argument is on the stack (cdecl).

* `init(state, outlen, key, keylen)` stores the initial hash value and, for
  a key, the key block in the buffer.
* `update(state, count, data, len, scratch)` fills the buffer; if more data
  follows, compresses it, compresses every block of `data` but the last
  straight from `data`, and copies that last one (1 to `B` bytes) to the
  buffer.
* `finalize(state, count, out, scratch)` pads the buffered block with zeros,
  compresses it as the last block, and writes the hash value to `out`.

The compression function (`name`, `code`: `compress(state, blocks, n, t,
last, scratch)`, BLAKE2s's or BLAKE2b's) is called with `scratch[0..512)` as
its scratch space. Each call pushes its seven arguments in a frame of their
own (`scratch` = `ebp`, `last` = `eax`, the high and low words of `t` =
`edx` and `ecx`, `n` = `edi`, `blocks` = `esi`, `state` = `ebx`), popped
(into `eax`) when it returns: with the return address the call stores, it
uses the 32 bytes below `esp`. The compression function preserves `ebx`,
`esi`, `edi` and `ebp`, so `ebx` (`state`) and `ebp` (`scratch`) live there
across it; our caller's values of those registers are saved in
`scratch[512..528)`, and the rest of the stream's variables in
`scratch[528..548)`: the byte count (low and high words), and the data
pointer, the bytes of data left and the bytes compressed straight from
`data` across the calls. Every address and branch depends only on `esp`,
the pointers, `count` and `len`.
-/

namespace VG.Impl.Blake2.X86.Stream

open VG.X86

section
variable (w : Nat)

/-- The size of a word in bytes. -/
def ws : Nat := w / 8
/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w

end

/-! ## The layout of `scratch` beyond the compression function's -/

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 512), (.esi, 516), (.edi, 520), (.ebp, 524)]
/-- The byte count, low and high words. -/
def cloOff : Nat := 528
def chiOff : Nat := 532
/-- The data pointer and the bytes of data left, across a call. -/
def dataOff : Nat := 536
def lenOff : Nat := 540
/-- The bytes compressed straight from `data`. -/
def bytesOff : Nat := 544

/-- Save the callee-saved registers, with `scratch` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `scratch` in `ebp` (copied to `eax` first). -/
def restore : List Instr := .mov .eax (.reg .ebp) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- `compress(ebx, esi, edi, ecx:edx, eax, ebp)`: its arguments pushed last
to first. -/
def compressCall (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx]) (.call name code) (.pop .eax 7)

section
variable (w : Nat)

/-- `eax` := the number of bytes in the buffer for the byte count whose low
word is in `eax` and high word in `ecx`: `((count - 1) mod B) + 1`, or 0 if
`count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.alu .or .ecx (.reg .eax)])
    (.ite .e (.block [.mov .eax (.imm 0)])
      (.block [.alu .sub .eax (.imm 1), .alu .and .eax (.imm (BitVec.ofNat 32 (B w - 1))),
        .alu .add .eax (.imm 1)]))

/-- The loop copying `cnt ≥ 1` bytes from `src` to the buffer at `dst` (`[dst +
N]`), through `tmp`. -/
def copyLoop (src dst cnt : Reg) (tmp : Reg8) : Prog isa :=
  .loop (.block [.movzx8 tmp.reg (at_ src 0), .store8 (at_ dst (N w)) tmp, .alu .add src (.imm 1),
    .alu .add dst (.imm 1), .alu .sub cnt (.imm 1)]) .ne

/-! ## `update`

Registers: `ebx` = `state`, `ebp` = `scratch`, `esi` = `data`, `edi` = bytes
of `data` left, `eax` = bytes in the buffer; the byte count is in
`scratch[528..536)`. -/

/-- Copy `min(B - eax, edi)` bytes of `data` to the buffer, adding them to the
byte count. -/
def fill : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.ofNat 32 (B w))), .alu .sub .ecx (.reg .eax),
      .alu .cmp .edi (.reg .ecx)])
  (.seq (.ite .b (.block [.mov .ecx (.reg .edi)]) (.block []))
  (.seq (.block [.alu .sub .edi (.reg .ecx), .mov .edx (.reg .ebx), .alu .add .edx (.reg .eax),
      .mov .eax (.mem (at_ .ebp cloOff)), .alu .add .eax (.reg .ecx), .store (at_ .ebp cloOff) .eax,
      .mov .eax (.mem (at_ .ebp chiOff)), .alu .adc .eax (.imm 0), .store (at_ .ebp chiOff) .eax,
      .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block []) (copyLoop w .esi .edx .ecx .al))))

/-- Compress the (full) buffer, which is not the last block: its counter is
the byte count. `data` and the bytes left are kept across the call. -/
def compressBuf (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.store (at_ .ebp dataOff) .esi, .store (at_ .ebp lenOff) .edi,
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 (N w))), .mov .edi (.imm 1),
      .mov .ecx (.mem (at_ .ebp cloOff)), .mov .edx (.mem (at_ .ebp chiOff)), .mov .eax (.imm 0)])
    (.seq (compressCall name code)
      (.block [.mov .esi (.mem (at_ .ebp dataOff)), .mov .edi (.mem (at_ .ebp lenOff))]))

/-- If the buffer is not empty: fill it, and if more data follows, compress
it. -/
def head (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (fill w) (.seq (.block [.alu .test .edi (.reg .edi)])
        (.ite .e (.block []) (compressBuf w name code)))))

/-- With the buffer empty and `edi ≥ 1` bytes left: compress all the blocks
of `data` but the last, `(edi - 1) / B` of them, straight from `data`: their
`(edi - 1) - ((edi - 1) mod B)` bytes, the first with the counter `count + B`. -/
def direct (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.reg .edi), .alu .sub .eax (.imm 1), .mov .ecx (.reg .eax),
      .alu .and .ecx (.imm (BitVec.ofNat 32 (B w - 1))), .alu .sub .eax (.reg .ecx)])
    (.ite .e (.block [])
      (.seq (.block [.store (at_ .ebp lenOff) .edi, .store (at_ .ebp bytesOff) .eax,
          .mov .edi (.reg .eax), .shift .shr .edi (Nat.log2 (B w)),
          .mov .ecx (.mem (at_ .ebp cloOff)), .alu .add .ecx (.imm (BitVec.ofNat 32 (B w))),
          .mov .edx (.mem (at_ .ebp chiOff)), .alu .adc .edx (.imm 0), .mov .eax (.imm 0)])
        (.seq (compressCall name code)
          (.block [.mov .eax (.mem (at_ .ebp bytesOff)), .alu .add .esi (.reg .eax),
            .mov .edi (.mem (at_ .ebp lenOff)), .alu .sub .edi (.reg .eax)]))))

/-- Copy the last `edi` (1 to `B`) bytes of `data` to the (empty) buffer. -/
def tail : Prog isa :=
  .seq (.block [.mov .ecx (.reg .edi), .mov .edx (.reg .ebx)]) (copyLoop w .esi .edx .ecx .al)

/-- The rest of `data`, if any, after `head`. -/
def rest (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .edi (.reg .edi)])
    (.ite .e (.block []) (.seq (direct w name code) (tail w)))

/-- Save registers, set up ours, and keep the byte count in `scratch`. -/
def updateStart : List Instr :=
  [.mov .eax (.mem (at_ .esp 24))] ++ save ++
  [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 16)),
   .mov .edi (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 8)), .store (at_ .ebp cloOff) .eax,
   .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp chiOff) .ecx]

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block updateStart) (.seq (bufLen w)
    (.seq (.block [.alu .test .edi (.reg .edi)])
      (.seq (.ite .e (.block []) (.seq (head w name code) (rest w name code))) (.block restore))))

/-! ## `finalize`

Registers: `ebx` = `state`, `ebp` = `scratch`. -/

/-- The loop zeroing the buffer from `edx` (`[edx + N]`) on, `ecx ≥ 1` bytes
(`eax = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (at_ .edx (N w)) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

/-- Zero the rest of the buffer, from byte `eax` on. -/
def pad : Prog isa :=
  .seq (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .eax),
      .mov .ecx (.imm (BitVec.ofNat 32 (B w))), .alu .sub .ecx (.reg .eax), .mov .eax (.imm 0)])
    (.ite .e (.block []) (zeroLoop w))

/-- Compress the buffer as the last block: its counter is the byte count. -/
def compressLast (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 (N w))),
      .mov .edi (.imm 1), .mov .eax (.imm 1), .mov .ecx (.mem (at_ .esp 8)),
      .mov .edx (.mem (at_ .esp 12))])
    (compressCall name code)

/-- Copy the hash value (at `ebx`) to `out` (at `eax`). -/
def output : List Instr :=
  (List.range (N w / 4)).flatMap fun k =>
    [.mov .ecx (.mem (at_ .ebx (4 * k))), .store (at_ .eax (4 * k)) .ecx]

def finalizeStart : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ save ++
  [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .esp 8)),
   .mov .ecx (.mem (at_ .esp 12))]

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block finalizeStart) (.seq (bufLen w) (.seq (pad w) (.seq (compressLast w name code)
    (.block (.mov .eax (.mem (at_ .esp 16)) :: output w ++ restore)))))

end

/-! ## `init`

Uses only `eax`, `ecx` and `edx`, and `ebx` while copying the key: our
caller's `ebx` is kept meanwhile in the first word of the hash value, which
is written last. -/

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- The `k`-th 32-bit word of the IV stored as `[u64; 8]` (BLAKE2b) or
`[u32; 8]` (BLAKE2s): little-endian, so the low half of a 64-bit word first. -/
def ivWord (k : Nat) : BitVec 32 := (P.IV[k / (w / 32)]!).extractLsb' (32 * (k % (w / 32))) 32

/-- `h := IV` (with the state at `eax`), then the parameter block
`0x0101kknn` XORed into `h[0]` (`kk` = `keylen` at `[esp + 16]`, `nn` =
`outlen` at `[esp + 8]`; `kk << 8` is a rotation, as `kk < 2^24`): only its
low 32-bit word changes. -/
def initState : List Instr :=
  (List.range (N w / 4)).flatMap (fun k => [.mov .ecx (.imm (ivWord P k)), .store (at_ .eax (4 * k)) .ecx]) ++
  [.mov .ecx (.mem (at_ .eax 0)), .alu .xor .ecx (.imm 0x01010000), .mov .edx (.mem (at_ .esp 16)),
   .shift .ror .edx 24, .alu .xor .ecx (.reg .edx), .alu .xor .ecx (.mem (at_ .esp 8)),
   .store (at_ .eax 0) .ecx]

/-- Zero the buffer and copy the `ecx ≥ 1` bytes of the key to it (with the
state at `eax`), through `ebx`. -/
def keyBlock : Prog isa :=
  .seq (.block (.mov .edx (.imm 0) :: ((List.range (B w / 4)).flatMap fun j =>
      [.store (at_ .eax (N w + 4 * j)) .edx]) ++
      [.store (at_ .eax 0) .ebx, .mov .edx (.mem (at_ .esp 12))]))
    (.seq (copyLoop w .edx .eax .ecx .bl)
      (.block [.mov .eax (.mem (at_ .esp 4)), .mov .ebx (.mem (at_ .eax 0))]))

def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 16)),
      .alu .test .ecx (.reg .ecx)])
    (.seq (.ite .e (.block []) (keyBlock (w := w)))
      (.block (.mov .eax (.mem (at_ .esp 4)) :: initState P)))

end

end VG.Impl.Blake2.X86.Stream
