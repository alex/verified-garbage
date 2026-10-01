import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86.Isa

/-!
# SHA-256 compression function: x86 (32-bit) implementation

`vg_sha256_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

With only seven usable registers, the working variables live in memory:
* `esi` points to the scratch buffer, `edi` to the current block, and `ebp`
  counts the blocks left; the state pointer is read from its argument slot
  when needed. These, and `esp`, are public; no address and no branch
  depends on anything else.
* `scratch[0..64)` is the 16-word message-schedule window, `scratch[64..96)`
  holds the working variables `a … h`, renamed between the fully unrolled
  rounds (in round `t`, variable `k` is at offset `var t k`), and
  `scratch[96..112)` holds the saved `ebx`, `esi`, `edi`, `ebp`.
* `eax`, `ebx`, `ecx` are the temporaries; `edx` retains `b ⊕ c` between
  rounds, so computing the majority needs one fewer scratch-buffer load.
-/

namespace VG.Impl.Sha256.X86

open VG.X86
open VG.Spec.Sha256 (K)

/-- The offset of working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Nat := 64 + 4 * ((k + 8 - t % 8) % 8)

/-- The offset of `W[i mod 16]`. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[esi + d]` -/
def sc (d : Nat) : Src := .mem (at_ .esi d)

/-- Store `Wₜ` in its slot. The additions are in the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .mov .eax (.mem (at_ .edi (4 * t))),
    .bswap .eax,
    .store (at_ .esi (slot t)) .eax]
  else [
    -- ebx := σ₁(Wₜ₋₂)
    .mov .eax (sc (slot (t + 14))),
    .mov .ebx (.reg .eax),
    .shift .ror .ebx 2,
    .alu .xor .ebx (.reg .eax),
    .shift .ror .ebx 17,
    .shift .shr .eax 10,
    .alu .xor .ebx (.reg .eax),
    -- ebx := ebx + Wₜ₋₇
    .alu .add .ebx (sc (slot (t + 9))),
    -- ebx := ebx + σ₀(Wₜ₋₁₅)
    .mov .eax (sc (slot (t + 1))),
    .mov .ecx (.reg .eax),
    .shift .ror .ecx 11,
    .alu .xor .ecx (.reg .eax),
    .shift .ror .ecx 7,
    .shift .shr .eax 3,
    .alu .xor .ecx (.reg .eax),
    .alu .add .ebx (.reg .ecx),
    -- ebx := ebx + Wₜ₋₁₆
    .alu .add .ebx (sc (slot t)),
    .store (at_ .esi (slot t)) .ebx]

/-- Round `t`. The additions are in the order of the specification. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- ebx := Σ₁(e), factoring the rotations as ROTR6(ROTR5(ROTR14(e) ⊕ e) ⊕ e)
    -- so a second temporary-register copy is unnecessary.
    .mov .eax (sc e),
    .mov .ebx (.reg .eax),
    .shift .ror .ebx 14,
    .alu .xor .ebx (.reg .eax),
    .shift .ror .ebx 5,
    .alu .xor .ebx (.reg .eax),
    .shift .ror .ebx 6,
    -- ecx := h + Σ₁(e)
    .mov .ecx (sc h),
    .alu .add .ecx (.reg .ebx),
    -- ecx := ecx + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .mov .ebx (sc f),
    .alu .xor .ebx (sc g),
    .alu .and .ebx (.reg .eax),
    .alu .xor .ebx (sc g),
    .alu .add .ecx (.reg .ebx),
    -- ecx := ecx + Kₜ + Wₜ, which is T₁
    .alu .add .ecx (.imm (K t)),
    .alu .add .ecx (sc (slot t)),
    -- e' := d + T₁
    .mov .ebx (sc d),
    .alu .add .ebx (.reg .ecx),
    .store (at_ .esi d) .ebx,
    -- ecx := ecx + Σ₀(a), similarly factored as ROTR2(ROTR11(ROTR9(a) ⊕ a) ⊕ a)
    .mov .eax (sc a),
    .mov .ebx (.reg .eax),
    .shift .ror .ebx 9,
    .alu .xor .ebx (.reg .eax),
    .shift .ror .ebx 11,
    .alu .xor .ebx (.reg .eax),
    .shift .ror .ebx 2,
    .alu .add .ecx (.reg .ebx),
    -- edx caches b ⊕ c; Maj = ((a ⊕ b) ∧ (b ⊕ c)) ⊕ b.
    .mov .ebx (.reg .eax),
    .alu .xor .ebx (sc b),
    .alu .and .edx (.reg .ebx),
    .alu .xor .edx (sc b),
    .alu .add .ecx (.reg .edx),
    -- The next round's b ⊕ c is this round's a ⊕ b.
    .mov .edx (.reg .ebx),
    .store (at_ .esi h) .ecx]

/-- Initialize the cached `b ⊕ c`, then execute rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block [.mov .edx (sc (var 0 1)), .alu .xor .edx (sc (var 0 2))]
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 96), (.esi, 100), (.edi, 104), (.ebp, 108)]

/-- Save the callee-saved registers, load the arguments, and set ZF if there
are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16))] ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)),
   .alu .test .ebp (.reg .ebp)]

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (sc 96), .mov .edi (sc 104), .mov .ebp (sc 108), .mov .esi (sc 100)]

/-- Copy the hash value into the working variables (`64 % 8 = 0`, so they are
in the same place after the 64 rounds). -/
def load : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap fun k => [.mov .ebx (.mem (at_ .eax (4 * k))), .store (at_ .esi (var 0 k)) .ebx]

/-- Add the working variables into the hash value. -/
def update : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap fun k => [
    .mov .ebx (sc (var 0 k)),
    .alu .add .ebx (.mem (at_ .eax (4 * k))),
    .store (at_ .eax (4 * k)) .ebx]

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .edi (.imm 64), .alu .sub .ebp (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sha256.X86
