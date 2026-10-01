import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Challenge
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Equation

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 ++
      Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 =
      Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem equation_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {challenge : List Byte}
    (hh : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = challenge) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith equationArgs "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation) s
      fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64) challenge) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (vs := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a1 := (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)
  have he : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 128) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 :=
    setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)
  refine WP.mono (equation_call hu hL ⟨a0, a1, a2, a3⟩) fun t ⟨ht, eq⟩ => ⟨ht, ?_⟩
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide),
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide), he, hh] at eq
  exact eq

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa body s fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
      (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat)
      (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64)) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun t ⟨ht, hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu, hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hL hr) fun v ⟨hv, he⟩ => ?_)
  rw [hashInput_eq] at he
  exact equation_step hv hL ha he

end VG.Proof.Ed25519.X86.VerifyMessage
