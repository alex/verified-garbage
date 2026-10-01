import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Reduce
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.Arm.VerifyMessage
import VerifiedGarbage.Proof.X25519.Bytes

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  unfold Spec.Ed25519.encodeLE Proof.X25519.leBytes
  apply congrArg (List.map · (List.range n))
  funext i
  rw [Nat.shiftRight_eq_div_pow,show 256^i=2^(8*i) by rw [Nat.pow_mul]]

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 38) (count := 8) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨State.addr L.E + 120, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 152) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [encodeLE_eq]
    have word (j : Nat) (hj : j < 8) : t.mem.readW (State.addr L.E + 152 + BitVec.ofNat 64 (4*j)) 32 = 0 := by
      have z := hz j hj
      have e : State.addr L.E + BitVec.ofNat 64 (4*(38+j)) = State.addr L.E + 152 + BitVec.ofNat 64 (4*j) := by
        rw [show 4*(38+j)=152+4*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    simpa using congrArg BitVec.toNat (word j hj)
  change Spec.X25519.bytesAt t.mem (State.addr L.E + 120) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 ++
    Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120 + 32) 32 = _
  rw [show State.addr L.E + 120 + 32 = State.addr L.E + 152 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.Arm.VerifyMessage
