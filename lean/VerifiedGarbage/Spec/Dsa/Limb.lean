/-!
# DSA big-integer arithmetic: 64-bit limb primitives

**Trusted.** These are building blocks for a future multi-limb Montgomery
implementation, not DSA operations on 64-bit domains. DSA p and q span
multiple limbs. The arithmetic uses all 64 bits; no limb is public.
-/
namespace VG.Spec.Dsa.Limb

/-- Low half of the unsigned 128-bit product. -/
def mulLo (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat)

/-- High half of the unsigned 128-bit product. -/
def mulHi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

/-- Bitwise selection: mask=0 selects a; mask=all-ones selects b.
Other masks select independently in each bit; they are not booleans. -/
def select (a b mask : BitVec 64) : BitVec 64 := a ^^^ ((a ^^^ b) &&& mask)

end VG.Spec.Dsa.Limb
