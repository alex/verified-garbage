import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry
import VerifiedGarbage.Proof.Framework.Contract

/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else
    if a = 0x900d then 0x30 else if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract X86.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState]
    sig_and_intros
    · decide +kernel
    · decide +kernel
    · change Spec.Ed25519.bytesAt satMem ((arg satState 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem ((arg satState 1).setWidth 64) 32)
      have a1 : arg satState 1 = 0x2000 := by decide
      have a2 : arg satState 2 = 0x3000 := by decide
      rw [a1, a2]
      change Spec.Ed25519.bytesAt satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem 0x2000 32)
      rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.X86.SignCached
