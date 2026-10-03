import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RC4 on AArch64, with the table in AdvSIMD registers

The 256-byte permutation lives in `v16`–`v31` throughout, rotated by a
public base `B` (a multiple of 16): byte `l` of `v(16 + r)` is `S[B + 16 r +
l]`. Nothing indexes memory with a secret:

* `j` is kept broadcast to every byte of `v0` (relative to `B`). A lookup
  `S[x]` is four `tbl`/`tbx` of four registers each, on `x`, `x ^ 64`,
  `x ^ 128` and `x ^ 192` (`v0`–`v3`): exactly one is in range.
* `S[j] := v` compares the lane numbers of each register (`v8`–`v11` hold
  0–15, …, 48–63) with the four indices (`cmeq`) and inserts `v` where they
  are equal (`bit`).
* `i` is public (the contract lets it leak). Bytes are processed sixteen at
  a time, one per lane of `v16`, whose lane `l` is then `S[i]`: `S[i] := v`
  is one `ins`, at a lane fixed in the code. After sixteen bytes the
  registers rotate by one and `B` advances by 16. The first group starts at
  lane `(i + 1) mod 16`: the lanes before it are skipped, as are the lanes
  after the data ends.

The PRGA keeps `S[i]` (broadcast, `v4`) for the next byte; the key schedule
runs the same steps from `i = 0`, with `B = 0` and no skipped lanes.
`v8`–`v13` are callee-saved: their low halves are kept in general-purpose
registers meanwhile. No instruction outside the baseline ISA is needed.
-/

namespace VG.Impl.Rc4.AArch64
open VG.AArch64

/-- The table register `r`. -/
def treg (r : Nat) : VReg :=
  [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD r .v16

/-- `j` relative to the base, broadcast; then `j ^ 64`, `j ^ 128`, `j ^ 192`. -/
def dq (q : Nat) : VReg := [.v0, .v1, .v2, .v3].getD q .v0

/-- The lane numbers `16 q … 16 q + 15`, for `q < 4`. -/
def lanes (q : Nat) : VReg := [.v8, .v9, .v10, .v11].getD q .v8

/-- `S[i]`, broadcast. -/
def si : VReg := .v4
/-- 64 and 128 in every byte. -/
def c64 : VReg := .v12
def c128 : VReg := .v13

def eorV (d n m : VReg) : Instr := .vop (.logic .eor d n m)

/-- `x ^ 64`, `x ^ 128` and `x ^ 192` of the index in `x`, into `a`, `b`, `c`. -/
def quarters (x a b c : VReg) : List Instr := [eorV a x c64, eorV b x c128, eorV c a c128]

/-- `d := S[x]`, broadcast, from the four indices `x`, `a`, `b`, `c`, using
`t` as a temporary. -/
def lookup (d t x a b c : VReg) : List Instr :=
  [.vop (.tblN false 4 d .v16 x), .vop (.tblN true 4 d .v20 a),
   .vop (.tblN false 4 t .v24 b), .vop (.tblN true 4 t .v28 c),
   .vop (.logic .orr d d t)]

/-- `S[j] := S[i]`: in every table register, at the lane equal to `j`. -/
def writeJ : List Instr :=
  (List.range 16).flatMap fun k =>
    [.vop (.cmeq .b16 .v7 (lanes (k % 4)) (dq (k / 4))), .vop (.bsel .bit (treg k) si .v7)]

/-- `-B`, broadcast, in the PRGA. -/
def negBase : VReg := .v14

/-- One swap, with `S[i]` in lane `l` of `v16`: `j += S[i]` (the key byte
too, already added, in the key schedule), `S[j]` into `v5`, `S[j] :=
S[i]`, the next `S[i]` (lane `l + 1`) into `v4`, and `S[i] := S[j]`. In
the PRGA (`prga`), `S[i] + S[j] - B` is left in `v6`. -/
def swapStep (prga : Bool) (l : Nat) : List Instr :=
  [.vop (.add .b16 (dq 0) (dq 0) si)] ++ quarters (dq 0) (dq 1) (dq 2) (dq 3) ++
  lookup .v5 .v6 (dq 0) (dq 1) (dq 2) (dq 3) ++ writeJ ++
  (if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) ++
  [.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16)),
   .vop (.insE .b16 (treg 0) l .v5 0)]

/-- The keystream byte `S[S[i] + S[j]]` (index in `v6`), XORed into the next
byte of the data at `x1`; advances `x1` and counts `x2` down. -/
def output : List Instr :=
  quarters .v6 .v1 .v2 .v3 ++ lookup .v7 .v1 .v6 .v1 .v2 .v3 ++
  [.umov .w .x6 .v7 0, .ldrb .x7 .x1 0, .logic .eor .w .x7 .x7 .x6, .strb .x7 .x1 0,
   .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- Rotate the table registers by one, and move `j` (and, in the PRGA,
`-B`) back by 16: the base advances by 16 (in `x8`). -/
def rotate (prga : Bool) : List Instr :=
  [.vop (.sub .b16 .v7 (lanes 1) (lanes 0)), .vop (.sub .b16 (dq 0) (dq 0) .v7)] ++
  (if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) ++
  [.vop (.mov .v7 (treg 0))] ++
  (List.range 15).map (fun r => .vop (.mov (treg r) (treg (r + 1)))) ++
  [.vop (.mov (treg 15) .v7), .addImm .x .x8 .x8 16]

/-! ## Constants -/

/-- `x6 := v`, a 64-bit constant. -/
def const64 (r : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x r (v.extractLsb' 0 16) 0, .movk .x r (v.extractLsb' 16 16) 1,
   .movk .x r (v.extractLsb' 32 16) 2, .movk .x r (v.extractLsb' 48 16) 3]

/-- The lane numbers in `v8`–`v11` and the broadcast 64 and 128 in `v12`,
`v13`, through `x6`, `x7` and `v7` (16 in every byte). -/
def constants : List Instr :=
  const64 .x6 0x0706050403020100 ++ const64 .x7 0x0f0e0d0c0b0a0908 ++
  [.vop (.ins .d2 (lanes 0) 0 .x6), .vop (.ins .d2 (lanes 0) 1 .x7),
   .movz .x .x6 16 0, .vop (.dup .b16 .v7 .x6),
   .vop (.add .b16 (lanes 1) (lanes 0) .v7), .vop (.add .b16 (lanes 2) (lanes 1) .v7),
   .vop (.add .b16 (lanes 3) (lanes 2) .v7),
   .movz .x .x6 64 0, .vop (.dup .b16 c64 .x6), .movz .x .x6 128 0, .vop (.dup .b16 c128 .x6)]

/-- The callee-saved registers `v8`–`v13` (and `v14` in the PRGA) used, and
where their low halves are kept. -/
def saved (prga : Bool) : List (VReg × Reg) :=
  [(.v8, .x10), (.v9, .x11), (.v10, .x14), (.v11, .x15), (.v12, .x16), (.v13, .x17)] ++
    if prga then [(negBase, .x3)] else []

def save (prga : Bool) : List Instr := (saved prga).map fun (v, r) => .umov .x r v 0
def restore (prga : Bool) : List Instr := (saved prga).map fun (v, r) => .vop (.ins .d2 v 0 r)

/-! ## The stream -/

/-- Lane `l` of a group: skipped while `x5` counts lanes to skip, and once
the data has ended. -/
def lane (l : Nat) : Prog isa :=
  .ite (.nonzero .x .x5) (.block [.subImm .x .x5 .x5 1])
    (.ite (.zero .x .x2) (.block []) (.block (swapStep true l ++ output)))

def lanesFrom : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (lanesFrom n) (lane n)

/-- Sixteen bytes, then the rotation. -/
def group : Prog isa := .seq (lanesFrom 16) (.block (rotate true))

/-- `x6 := (B + 16 r) mod 256` and `x7 := x0 + x6`: the address of table register `r`. -/
def rowAddr (r : Nat) : List Instr :=
  [.addImm .x .x6 .x8 (16 * r), .logic .and .x .x6 .x6 .x9, .add .x .x7 .x0 .x6]

def loadTable : List Instr := (List.range 16).flatMap fun r => rowAddr r ++ [.ldrq (treg r) .x7 0]
def storeTable : List Instr := (List.range 16).flatMap fun r => rowAddr r ++ [.strq (treg r) .x7 0]

/-- Save the callee-saved vector registers; read `i` and `j`; `x4 := i + len`,
the final `i`; `x5 := (i + 1) mod 16`, the lanes to skip; and
`x8 := B = (i + 1) mod 256 - x5`. -/
def applyLoad : List Instr :=
  save true ++
  [.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0,
   .add .x .x4 .x12 .x2,
   .addImm .x .x6 .x12 1, .logic .and .x .x6 .x6 .x9,
   .movz .x .x7 15 0, .logic .and .x .x5 .x6 .x7, .sub .x .x8 .x6 .x5]

/-- The table from `B`; the constants; `j - B` broadcast; `-B` broadcast;
and `S[i + 1]` broadcast, by a one-register `tbl` of `v16`. -/
def applySetup : List Instr :=
  loadTable ++ constants ++
  [.sub .x .x6 .x13 .x8, .vop (.dup .b16 (dq 0) .x6),
   .sub .x .x6 .x9 .x8, .addImm .x .x6 .x6 1, .vop (.dup .b16 negBase .x6),
   .vop (.dup .b16 .v7 .x5), .vop (.tbl si (treg 0) .v7)]

/-- Store the table, `i` and `j = (j - B) + B`. -/
def applyFinish : List Instr :=
  storeTable ++
  [.strb .x4 .x0 256, .umov .w .x6 (dq 0) 0, .add .x .x6 .x6 .x8, .strb .x6 .x0 257] ++
  restore true

/-- Everything after `applyLoad`, whose timing depends only on what it
computes from the public `i`. -/
def applyRest : Prog isa :=
  .seq (.block applySetup) (.seq (.loop group (.nonzero .x .x2)) (.block applyFinish))

/-- Streaming XOR, preserving the permutation and both PRGA indices. -/
def apply : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block applyLoad) applyRest)

/-! ## The key schedule

`vg_rc4_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/

/-- The next key byte, broadcast in `v6`, added to `j`: the key pointer `x7`
and the bytes left before the key repeats, `x5`. -/
def keyByte : Prog isa :=
  .seq (.block [.ldrb .x6 .x7 0, .vop (.dup .b16 .v6 .x6), .vop (.add .b16 (dq 0) (dq 0) .v6),
      .addImm .x .x7 .x7 1, .subImm .x .x5 .x5 1])
    (.ite (.zero .x .x5) (.block [.addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0]) (.block []))

def scheduleLanes : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (scheduleLanes n) (.seq keyByte (.block (swapStep false n)))

/-- Sixteen key-schedule swaps, then the rotation; `x4` counts the groups. -/
def scheduleGroup : Prog isa :=
  .seq (scheduleLanes 16) (.block (rotate false ++ [.subImm .x .x4 .x4 1]))

/-- The identity table, `j = 0`, `S[0] = 0`, the key pointer and length,
and 16 groups. -/
def scheduleSetup : List Instr :=
  save false ++ constants ++
  (List.range 4).map (fun r => .vop (.mov (treg r) (lanes r))) ++
  (List.range 4).map (fun r => eorV (treg (4 + r)) (lanes r) c64) ++
  (List.range 4).map (fun r => eorV (treg (8 + r)) (lanes r) c128) ++
  (List.range 4).map (fun r => eorV (treg (12 + r)) (treg (4 + r)) c128) ++
  [.vop (.movi0 (dq 0)), .vop (.movi0 si),
   .addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0, .movz .x .x4 16 0, .movz .x .x8 0 0]

/-- The table (whose registers are back where they started: `x8 = 256`) at
`x0 := ctx`, and zero for both PRGA indices and the result. -/
def scheduleFinish : List Instr :=
  [.addImm .x .x0 .x2 0, .movz .x .x9 255 0] ++ storeTable ++
  [.movz .w .x6 0 0, .strb .x6 .x0 256, .strb .x6 .x0 257, .movz .w .x0 0 0] ++ restore false

/-- Key scheduling after the public key-length check succeeds. -/
def initValid : Prog isa :=
  .seq (.block scheduleSetup) (.seq (.loop scheduleGroup (.nonzero .x .x4)) (.block scheduleFinish))

/-- Checked key scheduling; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8])
    (.ite (.nonzero .x .x4) (.block [.movz .w .x0 1 0]) initValid)

end VG.Impl.Rc4.AArch64
