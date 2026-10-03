import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# Deterministic ECDSA (RFC 6979) on x86-64

`sign R H core (out = rdi, d = rsi, digest = rdx, scratch = rcx) -> eax`, for
a curve of 32-byte scalars and a Merkle–Damgård hash function `H` of at least
32 bytes of output (one `V` makes a candidate: `blocks = 1`): RFC 6979 §3.2,
with HMAC computed by calling `H`'s HMAC `init`, streaming `update` and HMAC
`finalize`, and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign`).

Everything runs in one stack frame of 17 words, pushed from `rdi`, `rsi`,
`rdx`, `rcx` and 13 copies of `rax`: from `rsp`, `K`, `V` and `h` (the
hash's leftmost 32 bytes reduced modulo `n`, `bits2octets`), 32 bytes each,
the number of candidates left, then `scratch`, `digest`, `d` and `out`. The
calls use only `scratch`, which `core` overwrites entirely, and the frame,
which they cannot change; `K`, `V` and `h` are cleared before the frame is
popped. In `scratch`: HMAC's inner and outer streaming states, the working
space of HMAC's and `H`'s functions, and the message of steps d, f and h.3.

1. `h = bits2octets(digest)`: the leftmost 32 bytes, minus `n` if they are
   at least `n` (a conditional subtraction, as `2^256 < 2n`).
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`.
3. At most `tries` times: `V = HMAC_K(V)`, the candidate `k = V`, and
   `core(out, d, digest, V, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on is
   computed without branches, so that the code branches only on it: the
   number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its return value is ours.

A block addresses memory only at `rsp` or at a pointer an earlier block
loaded from the frame (`digestPtr`, `msgPtrs`), never one it loads itself,
so that the taint analysis of each block knows its addresses are public.
-/

namespace VG.Impl.Ecdsa.Rfc6979.X86_64

open VG.X86_64 VG.Impl.Pbkdf2.Md.X86_64

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! Where things are in the frame. -/
def fK : Nat := 0
def fV : Nat := 32
def fH : Nat := 64
def fCnt : Nat := 96
def fScratch : Nat := 104
def fDigest : Nat := 112
def fD : Nat := 120
def fOut : Nat := 128

/-! Where things are in `scratch`. -/
def sInner : Nat := 0
def sOuter : Nat := 96
def sWork : Nat := 192
def sMsg : Nat := 1024

/-- What the code needs of a curve and a hash function. -/
structure Cfg where
  /-- The hash function's code and names. -/
  H : Hash
  /-- The order of the curve's base point. -/
  n : Nat
  /-- The most candidates to try. -/
  tries : Nat
  /-- The signature with a given `k`, and its name. -/
  coreN : String
  coreC : Prog isa

namespace Cfg

variable (c : Cfg)

/-- `d ← [rsp + o] + a`: an address in `scratch`. -/
def scr (d : Reg) (a : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 a))]

/-- `d ← rsp + o`: an address in the frame. -/
def fr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.reg .rsp), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `HMAC_K(data)` into the frame at `dst`, for `len` bytes of `data` at the
address `dataA` sets `rdx` to: HMAC's `init` with the key `K`, `update` on
the inner state, and `finalize`. -/
def hmac (dataA : List Instr) (len dst : Nat) : Prog isa :=
  .seq (.block (scr .rdi sInner ++ scr .rsi sOuter ++ fr .rdx fK ++
      [.mov32 .rcx (.imm 32)] ++ scr .r8 sWork))
  (.seq (.call c.H.hmacInitN c.H.hmacInit)
  (.seq (.block (scr .rdi sInner ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 c.H.P.B))] ++ dataA ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 len))] ++ scr .r8 sWork))
  (.seq (.call c.H.updN c.H.updC)
  (.seq (.block (scr .rdi sInner ++ scr .rsi sOuter ++
      [.mov32 .rdx (.imm (BitVec.ofNat 32 (c.H.P.B + len)))] ++ fr .rcx dst ++ scr .r8 sWork))
    (.call c.H.hmacFinN c.H.hmacFin)))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac (fr .rdx fV) 32 fV

/-- Word `j` of the 32 bytes at `[src + so]` to `[dst + d]`, through `rax`. -/
def copy4 (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : List Instr :=
  (List.range 4).flatMap fun j =>
    [.mov .rax (.mem (at_ src (so + 8 * j))), .store (at_ dst (d + 8 * j)) .rax]

/-- The pointers the messages need: `scratch` in `rdi`, `d` in `rsi` (loaded
first, so that every address the message's block computes is from them or
`rsp`). -/
def msgPtrs : List Instr := [.mov .rdi (.mem (stk fScratch)), .mov .rsi (.mem (stk fD))]

/-- The message `V ‖ b` (and `‖ d ‖ h` if `full`) at `scratch + sMsg`, with
`scratch` in `rdi` and `d` in `rsi`: `V` and `h` from the frame, `b` a byte. -/
def msg (b : Nat) (full : Bool) : List Instr :=
  copy4 .rsp fV .rdi sMsg ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + 32)) .rax] ++
    (if full then copy4 .rsi 0 .rdi (sMsg + 33) ++ copy4 .rsp fH .rdi (sMsg + 65) else [])

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg b true)) (.seq (c.hmac (scr .rdx sMsg) 97 fK) c.hmacV))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block msgPtrs) (.seq (.block (msg 0 false)) (.seq (c.hmac (scr .rdx sMsg) 33 fK) c.hmacV))

/-- The 64-bit words of `n`, least significant first. -/
def nWord (j : Nat) : BitVec 64 := BitVec.ofNat 64 (c.n >>> (64 * j))

/-- `digest` in `rsi`. -/
def digestPtr : List Instr := [.mov .rsi (.mem (stk fDigest))]

/-- `h`: the 32 bytes at `digest` (in `rsi`), as a big-endian number in
`r11:r10:r9:r8`, minus `n` (in `rsi:rdi:rcx:rax`) if that does not borrow,
back big-endian into the frame. -/
def reduce : List Instr :=
  [.mov .r8 (.mem (at_ .rsi 24)), .bswap .r8, .mov .r9 (.mem (at_ .rsi 16)), .bswap .r9,
    .mov .r10 (.mem (at_ .rsi 8)), .bswap .r10, .mov .r11 (.mem (at_ .rsi 0)), .bswap .r11,
    .movImm64 .rdx (c.nWord 0), .mov .rax (.reg .r8), .alu .sub .rax (.reg .rdx),
    .movImm64 .rdx (c.nWord 1), .mov .rcx (.reg .r9), .alu .sbb .rcx (.reg .rdx),
    .movImm64 .rdx (c.nWord 2), .mov .rdi (.reg .r10), .alu .sbb .rdi (.reg .rdx),
    .movImm64 .rdx (c.nWord 3), .mov .rsi (.reg .r11), .alu .sbb .rsi (.reg .rdx),
    .alu .sbb .rdx (.reg .rdx)] ++
  -- `x = d ^ ((x ^ d) & mask)`: `x` if it borrowed, `d` if not.
  ([(.r8, .rax), (.r9, .rcx), (.r10, .rdi), (.r11, .rsi)] : List (Reg × Reg)).flatMap
    (fun (x, d) => [.alu .xor x (.reg d), .alu .and x (.reg .rdx), .alu .xor x (.reg d)]) ++
  [.bswap .r11, .store (stk fH) .r11, .bswap .r10, .store (stk (fH + 8)) .r10,
    .bswap .r9, .store (stk (fH + 16)) .r9, .bswap .r8, .store (stk (fH + 24)) .r8]

/-- `V = 0x01…`, `K = 0x00…`. -/
def initKV : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)] ++
    (List.range 4).flatMap fun j => [.store (stk (fV + 8 * j)) .rax, .store (stk (fK + 8 * j)) .rcx]

/-- The candidates left. -/
def initCnt : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 c.tries)), .store (stk fCnt) .rax]

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.mem (stk fD)), .mov .rdx (.mem (stk fDigest))] ++
    fr .rcx fV ++ [.mov .r8 (.mem (stk fScratch))]

/-- One candidate fewer, and `rdx ≠ 0` (and `ZF` clear) iff the signature
failed (`eax = 0`) and candidates are left: `rdx = -(eax < 1) & (count - 1)`. -/
def goOn : List Instr :=
  [.mov .rcx (.mem (stk fCnt)), .alu .sub .rcx (.imm 1), .store (stk fCnt) .rcx,
    .alu32 .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.reg .rcx),
    .alu .test .rdx (.reg .rdx)]

/-- `ZF` clear: go on. -/
def again : List Instr := [.mov32 .rdx (.imm 1), .alu .test .rdx (.reg .rdx)]

/-- `ZF` set: stop. -/
def stop : List Instr := [.alu32 .xor .rdx (.reg .rdx)]

/-- One candidate: `V = HMAC_K(V)`, `core` with `k = V`, then, if it failed
and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite .ne (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared (`rax`, the result, kept). -/
def wipe : List Instr :=
  [.alu32 .xor .rcx (.reg .rcx)] ++ (List.range 12).map fun j => .store (stk (8 * j)) .rcx

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block digestPtr)
  (.seq (.block (c.reduce ++ initKV))
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne .ne)
    (.block wipe))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa :=
  .frame (.push ([.rdi, .rsi, .rdx, .rcx] ++ List.replicate 13 .rax)) c.body (.pop .rcx 17)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.X86_64
