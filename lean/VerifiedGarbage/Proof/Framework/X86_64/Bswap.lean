import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# `bswap` of a little-endian load is a big-endian load

`bswap32` and `bswap64` are `byteRev32` and `byteRev64`, whose lemmas are in
`Proof/Framework/Bswap.lean`.
-/

namespace VG.X86_64

/-- A 32-bit load followed by `bswap` reads the four bytes big-endian. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    bswap32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  byteRev32_readW m a

/-- A 64-bit load followed by `bswap` reads the eight bytes big-endian. -/
theorem bswap64_readW (m : Mem) (a : Addr) :
    bswap64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  byteRev64_readW m a

end VG.X86_64
