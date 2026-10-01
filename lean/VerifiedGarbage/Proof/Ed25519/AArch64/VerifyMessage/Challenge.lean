import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.AArch64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : Ctx L g v m₀ s) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 20) (count := 4) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.AArch64.encodeLE_eq]
    have word (j : Nat) (hj : j < 4) : t.mem.readW (L.E + 160 + BitVec.ofNat 64 (8*j)) 64 = 0 := by
      have z := hz j hj
      have e : L.E + BitVec.ofNat 64 (8*(20+j)) = L.E + 160 + BitVec.ofNat 64 (8*j) := by
        rw [show 8*(20+j)=160+8*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words64
    · have z := word 0 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 1 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 2 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 3 (by decide)
      simpa using congrArg BitVec.toNat z
  change Spec.X25519.bytesAt t.mem (L.E + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E + 128 + 32) 32 = _
  rw [show L.E + 128 + 32 = L.E + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.AArch64.VerifyMessage
