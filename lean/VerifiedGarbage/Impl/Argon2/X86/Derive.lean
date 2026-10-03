import VerifiedGarbage.Impl.Argon2.X86.Fill

/-!
# Argon2 on x86 (32-bit): the derivation

`vg_argon2(kind, password, password_len, salt, salt_len, iterations,
memory_cost, lanes, threads, secret, secret_len, associated_data, ad_len,
memory, blocks, scratch, out, out_len)`, cdecl.

The caller's `ebp`, `edi`, `esi` and `ebx` are pushed in frames of their own,
then the locals (`Impl/Argon2/X86/Layout.lean`), at which `ebp` points
throughout. The derivation computes the parameters and H₀, initializes the
memory, fills it, XORs the last block of every lane into the first block of
the memory, and writes H′ of it to `out`. The lanes are evaluated serially,
which every positive `threads` permits.
-/

namespace VG.Impl.Argon2.X86.Derive

open VG.X86
open VG.Impl.Sha512.X86 (at_)

/-! ## The final block and the tag -/

/-- Zero the memory's first block. -/
def reduceClear : List Instr :=
  [.mov .edi (fr (argOff memoryArg)), .mov .eax (.imm 0)] ++
    (List.range 256).map fun k => .store (at_ .edi (4 * k)) .eax

/-- XOR the last block of lane `[ebp + laneOff]` into the first block. -/
def reduceLane : List Instr :=
  [.mov .eax (fr laneOff), .mov .ecx (fr laneLenOff), .alu .sub .ecx (.imm 1)] ++ blockAddr ++
    [.mov .esi (.reg .eax), .mov .edi (fr (argOff memoryArg))] ++ writeBlock true

def reduce : Prog isa :=
  .seq (.block (reduceClear ++ setLocal laneOff 0))
    (.loop (.block (reduceLane ++ advance laneOff (fr (argOff lanesArg)))) .b)

/-- `hprime(memory, 1024, out, out_len, scratch)`. -/
def finalOutput : Prog isa :=
  .seq (.block [.mov .esi (fr (argOff memoryArg)), .mov .eax (.imm 1024), .mov .edi (fr (argOff outArg)),
      .mov .ecx (fr (argOff outLenArg)), .mov .edx (fr (argOff scratchArg))])
    (.frame (.push [.edx, .ecx, .edi, .eax, .esi]) (.call hPrimeName HPrime.code) (.pop .eax 5))

/-! ## The whole function -/

def body : Prog isa :=
  .seq (.block (.mov .ebp (.reg .esp) :: parameters))
  (.seq code
  (.seq memoryInit
  (.seq passesLoop
  (.seq reduce finalOutput))))

/-- The registers saved, each in a frame of its own (so that each pop restores
one), around the locals. -/
def saved : List Reg := [.ebp, .edi, .esi, .ebx]

def frames (c : Prog isa) : List Reg → Prog isa
  | [] => .frame (.push (List.replicate (locals / 4) .eax)) c (.pop .eax (locals / 4))
  | r :: rs => .frame (.push [r]) (frames c rs) (.pop r 1)

def derive : Prog isa := frames body saved

end VG.Impl.Argon2.X86.Derive
