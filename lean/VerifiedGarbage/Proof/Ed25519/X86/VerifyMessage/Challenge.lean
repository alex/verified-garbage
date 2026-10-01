import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.HashPipeline
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.X86.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem setup_bytes {u : State} {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) (hd : 24 ≤ d) (hn : d + n ≤ 256) :
    Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint _ hd (by omega)).symm) (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce) s
      fun t => Ctx L g m₀ t ∧ Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame 128, .frame 192, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := (hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _)
  have H := hashSpace hL
  refine WP.mono (Whole.reduce_call hu H (by simp [Lay.outputs]) (d := 128)
    (by decide) (by decide) a0 a1 a2) fun t ⟨ht, _, hd⟩ => ⟨ht, ?_⟩
  have e128 : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  have e192 : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 := Whole.frame_addr H.frameFit (by decide : 192 < 256)
  change Spec.Ed25519.bytesAt t.mem ((L.E + 128).setWidth 64) 32 = _ at hd
  have same : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 192) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 :=
    setup_bytes hf (by decide : 24 ≤ 192) (by decide : 192 + 64 ≤ 256)
  rw [e128, e192, same] at hd
  exact hd

theorem extend_step (hc : Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 40) (count := 8)
    (hashSpace hL).frameFit (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E.setWidth 64 + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.X86.encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    have z := hz j hj
    rw [addr_eq (by have := hL.top; omega)] at z
    have e : L.E.setWidth 64 + BitVec.ofNat 64 (4 * (40 + j)) =
        L.E.setWidth 64 + 160 + BitVec.ofNat 64 (4 * j) := by
      rw [show 4 * (40 + j) = 160 + 4 * j by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e] at z
    rw [z]
    simp
  change Spec.X25519.bytesAt t.mem (L.E.setWidth 64 + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128 + 32) 32 = _
  rw [show L.E.setWidth 64 + 128 + 32 = L.E.setWidth 64 + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.X86.VerifyMessage
