import VerifiedGarbage.Spec.Argon2

/-! The input block of the reviewed independent-address specification. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def addressInput (p : Params) (pass lane slice counter : Nat) : Block :=
  zeroBlock |>.set 0 (BitVec.ofNat 64 pass) |>.set 1 (BitVec.ofNat 64 lane)
    |>.set 2 (BitVec.ofNat 64 slice) |>.set 3 (BitVec.ofNat 64 p.blocks)
    |>.set 4 (BitVec.ofNat 64 p.passes) |>.set 5 (BitVec.ofNat 64 p.variant.code)
    |>.set 6 (BitVec.ofNat 64 counter)

theorem addressBlock_eq (p : Params) (pass lane slice counter : Nat) :
    addressBlock p pass lane slice counter =
      compress zeroBlock (compress zeroBlock (addressInput p pass lane slice counter)) := rfl

end VG.Proof.Argon2
