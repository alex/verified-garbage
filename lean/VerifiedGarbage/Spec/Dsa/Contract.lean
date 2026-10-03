import VerifiedGarbage.Spec.Dsa.Limb
import VerifiedGarbage.TCB.Artifact

/-! # Initial DSA arithmetic contracts (trusted)
All arguments, including the selection mask, are secret. No memory is
accessed and no stack is used. Contracts cover every target; a future registration can supply
an x86-64 baseline implementation. -/

namespace VG.Spec.Dsa.Limb

def mulSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false)]
  ret := some .u64

def mulLoContract {M : ISA} (A : Abi M) : Contract M :=
  mulSig.contract A (post := fun a b m m' r => r = mulLo a b ∧ m' = m)

def mulHiContract {M : ISA} (A : Abi M) : Contract M :=
  mulSig.contract A (post := fun a b m m' r => r = mulHi a b ∧ m' = m)

def selectSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false), ("mask", .int .u64 false)]
  ret := some .u64

def selectContract {M : ISA} (A : Abi M) : Contract M :=
  selectSig.contract A (post := fun a b mask m m' r => r = select a b mask ∧ m' = m)

def mulLoApi : Api where
  module := "dsa"
  name := "vg_dsa_limb_mul_lo"
  sig := mulSig
  contracts := some fun A _ => mulLoContract A
  summary := "Returns the low 64 bits of the unsigned product of two secret limbs. \
    Writes no memory.\n\nContract: `VG.Spec.Dsa.Limb.mulLoContract`. \
    Constant time: neither operand affects the leakage trace."
  safety := []

def mulHiApi : Api where
  module := "dsa"
  name := "vg_dsa_limb_mul_hi"
  sig := mulSig
  contracts := some fun A _ => mulHiContract A
  summary := "Returns the high 64 bits of the unsigned product of two secret limbs. \
    Writes no memory.\n\nContract: `VG.Spec.Dsa.Limb.mulHiContract`. \
    Constant time: neither operand affects the leakage trace."
  safety := []

def selectApi : Api where
  module := "dsa"
  name := "vg_dsa_limb_select"
  sig := selectSig
  contracts := some fun A _ => selectContract A
  summary := "Selects bits of two secret limbs: a zero mask bit selects `a`, a one \
    selects `b`. A zero mask selects `a`; an all-ones mask selects `b`. Writes no memory.\n\n\
    Contract: `VG.Spec.Dsa.Limb.selectContract`. \
    Constant time: operands and mask do not affect the leakage trace."
  safety := []

end VG.Spec.Dsa.Limb
