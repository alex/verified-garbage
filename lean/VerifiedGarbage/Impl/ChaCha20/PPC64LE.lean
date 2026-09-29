import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ChaCha20 block function: PPC64LE implementation

`vg_chacha20_block(state = r3, buf = r4)`.

* Word `k` of the state lives in the low word of `wreg k` (`r5`–`r12`,
  `r14`–`r21`) throughout; the ten double rounds are fully unrolled. The
  additions act on all 64 bits, so the high words of the registers hold
  carries, which the rotations (`rlwinm`, which reads the low word and
  zero-extends) and the word stores ignore.
* `r14`–`r21` are nonvolatile: they are saved in `buf[16..32)` (bytes 64 to
  127, which are working space) first and restored last. Only the first 64
  bytes of `buf` are written otherwise.
* The input state is re-read from `state` to add it at the end, using `r0`
  as a temporary.
* Every address is `r3` or `r4` plus a constant, and there are no branches,
  so only the pointers can affect timing.
-/

namespace VG.Impl.ChaCha20.PPC64LE

open VG.PPC64LE

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21].getD
    k .r5

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21].getD i .r14

/-- Save them in `buf[64..128)`. -/
def save : List Instr := (List.range 8).flatMap fun i => [.store .d (saved i) .r4 (64 + 8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 8).flatMap fun i => [.load .d (saved i) .r4 (64 + 8 * i)]

/-- The quarter round (RFC 8439 §2.1) on the low words of `a, b, c, d`. A
rotation left by `k` is a rotation right by `32 - k`. -/
def qr (a b c d : Reg) : List Instr := [
  .add a a b, .logic .xor d d a, .rotr .w d d 16,
  .add c c d, .logic .xor b b c, .rotr .w b b 20,
  .add a a b, .logic .xor d d a, .rotr .w d d 24,
  .add c c d, .logic .xor b b c, .rotr .w b b 25]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2). -/
def quarter (x y z w : Nat) : Prog isa := .block (qr (wreg x) (wreg y) (wreg z) (wreg w))

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (quarter 2 6 10 14) <|
  .seq (quarter 3 7 11 15) <| .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Load the state into the registers. -/
def load : List Instr := (List.range 16).flatMap fun k => [.load .w (wreg k) .r3 (4 * k)]

/-- Add input word `k` (via `r0`) and store output word `k`. -/
def addWord (k : Nat) : List Instr :=
  [.load .w .r0 .r3 (4 * k), .add (wreg k) (wreg k) .r0, .store .w (wreg k) .r4 (4 * k)]

def finish : List Instr := (List.range 16).flatMap addWord

/-- Load, run the rounds and add. -/
def main : Prog isa := .seq (.block load) (.seq (rounds 10) (.block finish))

def block : Prog isa := .seq (.block save) (.seq main (.block restore))

end VG.Impl.ChaCha20.PPC64LE
