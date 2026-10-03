import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Zeroization: PPC64LE implementation

`vg_zeroize(p = r3, len = r4)`: doubleword stores (`std`), then a byte tail
(`stb`), as on AArch64. Stores to normal memory may be unaligned. The loops
count down to zero, and only `p` and `len` decide the branches and addresses.
-/

namespace VG.Impl.Zeroize.PPC64LE
open VG.PPC64LE

def step (word : Bool) : List Instr :=
  [if word then .store .d .r5 .r3 0 else .stb .r5 .r3 0,
   .addi .r3 .r3 (if word then 8 else 1), .subi .r6 .r6 1]

def loop (word : Bool) : Prog isa :=
  .ite (.zero .d .r6) (.block []) (.loop (.block (step word)) (.nonzero .d .r6))

def zeroize : Prog isa :=
  .seq (.block [.li .r5 0, .lsr .d .r6 .r4 3, .li .r7 7, .logic .and .r4 .r4 .r7])
    (.seq (loop true) (.seq (.block [.addi .r6 .r4 0]) (loop false)))

end VG.Impl.Zeroize.PPC64LE
