import VerifiedGarbage.Impl.Aes.X86.Ctr32

/-!
# The AES key expansion on x86 (32-bit)

`vg_aes_expand_key(key, key_len, schedule, scratch)`, cdecl: the arguments
are at `[esp + 4]` … `[esp + 16]`.

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in slot 0 (as BearSSL's
`aes_ct` does in its `sub_word`; Thomas Pornin, MIT licence), the other
slots zero. `edi` points to the scratch buffer throughout; its bytes from
256 on hold the saved registers (as in `Ctr32.lean`), then:

* `[272, 276)`: the round constant;
* `[276, 280)`: `4 (i mod Nk)` for the word `i` being computed;
* `[280, 284)`: `4 Nk`, the key's length;
* `[284, 288)`: the number of words left.

The key is copied into the schedule a word at a time. Word `i` (from `Nk`
on) is computed with `esi` at `w[i − 1]`. Every branch is on the counters,
which depend only on `key_len`; the key's bytes only ever reach the S-box's
registers and memory. The counters are in `ecx`, `edx` and `ebp` while
`w[i]` is written, and stored back after.
-/

namespace VG.Impl.Aes.X86

open VG.X86

def rcOff : Nat := 272
def jmOff : Nat := 276
def nkOff : Nat := 280
def leftOff : Nat := 284

/-- Copy the key (`key_len` bytes, a multiple of 4) to the schedule: `esi`
and `ebp` walk them, and `ecx` counts the bytes left. -/
def copySetup : List Instr :=
  [.mov .esi (.mem (argOp 0)), .mov .ebp (.mem (argOp 2)), .mov .ecx (.mem (argOp 1))]

def copyBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, addI .esi 4, addI .ebp 4, subI .ecx 4]

/-- After the copy (`ebp` at `w[Nk]`): `esi := ` the address of `w[Nk − 1]`;
`4 (i mod Nk) = 0`, `4 Nk`, the `4 (Nr + 1) − Nk = 3 Nk + 28` words left,
and the round constant 1. -/
def wordSetup : List Instr :=
  [movR .esi .ebp, subI .esi 4, movI .eax 0, .store (at_ .edi jmOff) .eax,
   .mov .eax (.mem (argOp 1)), .store (at_ .edi nkOff) .eax,
   shrI .eax 2, movR .ebx .eax, addR .eax .eax, addR .eax .ebx, addI .eax 28,
   .store (at_ .edi leftOff) .eax, movI .eax 1, .store (at_ .edi rcOff) .eax]

/-- The S-box on each byte of `eax`: in slot 0, with slots 1–7 zero. -/
def subWordCode : List Instr :=
  [st 0 .eax, movI .eax 0] ++ (List.range 7).map (fun k => st (k + 1) .eax) ++
    ortho ++ sboxCode ++ ortho ++ [movS .eax 0]

/-- After `subWordCode`: `eax := ROTWORD(eax) ⊕ Rcon`, and the round constant
times `x` (without a branch: `{1b}` is XORed in under a mask made from bit 7). -/
def rotTail : List Instr :=
  [rorI .eax 8, .alu .xor .eax (.mem (at_ .edi rcOff)),
   .mov .ebx (.mem (at_ .edi rcOff)), movR .ecx .ebx, shrI .ecx 7, movI .edx 0, subR .edx .ecx,
   andI .edx 0x1b, addR .ebx .ebx, xorR .ebx .edx, andI .ebx 0xff, .store (at_ .edi rcOff) .ebx]

/-- `eax := SUBWORD(ROTWORD(eax)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subWordCode ++ rotTail

/-- `w[i] := w[i − Nk] ⊕ eax`, with the counters in registers, and on to
`i + 1` (ZF is set after the last word). -/
def wordStore : Prog isa :=
  .seq (.block
      [.mov .ecx (.mem (at_ .edi nkOff)), movR .ebx .esi, addI .ebx 4, subR .ebx .ecx,
       .alu .xor .eax (.mem (at_ .ebx 0)),
       .mov .ecx (.mem (at_ .edi jmOff)), .mov .edx (.mem (at_ .edi leftOff)),
       .mov .ebp (.mem (at_ .edi nkOff)),
       .store (at_ .esi 4) .eax, addI .esi 4, addI .ecx 4, .alu .cmp .ecx (.reg .ebp)])
    (.seq (.ite .e (.block [movI .ecx 0]) (.block []))
      (.block [.store (at_ .edi jmOff) .ecx, .store (at_ .edi nkOff) .ebp,
        subI .edx 1, .store (at_ .edi leftOff) .edx]))

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; then `wordStore`. -/
def wordBody : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .edi jmOff)),
      .alu .test .ecx (.reg .ecx)])
    (.seq (.ite .e (.block rotWordStep)
        (.seq (.block [.alu .cmp .ecx (.imm 16)])
          (.ite .e (.seq (.block [.mov .ecx (.mem (at_ .edi nkOff)), .alu .cmp .ecx (.imm 32)])
              (.ite .e (.block subWordCode) (.block [])))
            (.block []))))
      wordStore)

def expandKey : Prog isa :=
  .seq (.block (saveRegs 3 ++ copySetup))
    (.seq (.loop (.block copyBody) .ne)
      (.seq (.block wordSetup)
        (.seq (.loop wordBody .ne) (.block restoreRegs))))

end VG.Impl.Aes.X86
