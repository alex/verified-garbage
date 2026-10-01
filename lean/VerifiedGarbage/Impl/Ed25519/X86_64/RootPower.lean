import VerifiedGarbage.Impl.X25519.X86_64

/-! The RFC 8032 square-root exponent, using the field inversion addition chain. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64 VG.Impl.X25519.X86_64

def rootPower : Prog isa :=
  .seq (.block (mul T0 Z2 Z2)) <|                           -- z^2
  .seq (.block (mul T1 T0 T0 ++ mul T1 T1 T1)) <|           -- z^8
  .seq (.block (mul T1 Z2 T1 ++ mul T0 T0 T1 ++             -- z^9, z^11
    mul T2 T0 T0 ++ mul T1 T1 T2)) <|                       -- z^22, z^(2^5 - 1)
  .seq (sqn baseline T2 T1 5) <| .seq (.block (mul T1 T2 T1)) <|      -- z^(2^10 - 1)
  .seq (sqn baseline T2 T1 10) <| .seq (.block (mul T2 T2 T1)) <|     -- z^(2^20 - 1)
  .seq (sqn baseline T3 T2 20) <| .seq (.block (mul T2 T3 T2)) <|     -- z^(2^40 - 1)
  .seq (sqn baseline T2 T2 10) <| .seq (.block (mul T1 T2 T1)) <|     -- z^(2^50 - 1)
  .seq (sqn baseline T2 T1 50) <| .seq (.block (mul T2 T2 T1)) <|     -- z^(2^100 - 1)
  .seq (sqn baseline T3 T2 100) <| .seq (.block (mul T2 T3 T2)) <|    -- z^(2^200 - 1)
  .seq (sqn baseline T2 T2 50) <| .seq (.block (mul T1 T2 T1)) <|     -- z^(2^250 - 1)
  .seq (sqn baseline T1 T1 2) (.block (mul T1 T1 Z2))                -- z^(2^252 - 3)

end VG.Impl.Ed25519.X86_64
