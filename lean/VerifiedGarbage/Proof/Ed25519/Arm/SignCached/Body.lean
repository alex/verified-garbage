import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashFrame
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Reduce
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.MulAdd
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Secret
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe

/-! Merged from `Proof.Ed25519.Arm.SignCached.PrimitiveSteps`. -/
section
namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : d + 32 ≤ 184) :
    WP isa (reduce d) s fun t => Ctx L g m₀ t ∧ Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha
    (args := [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)])
    (by simp) (by simp [Whole.valid]; omega) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .frame d) (by simp)
  have a1 := hs (.r1, .frame 184) (by simp)
  have a2 := hs (.r2, .caller 5 0) (by simp)
  change u.gpr .r2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL hd ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

theorem base_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith baseArgs "vg_ed25519_scalar_base" VG.Impl.Ed25519.Arm.scalarBase) s
      fun t => Ctx L g m₀ t ∧ Frame (baseWr L) s.mem t.mem ∧
        Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 =
          Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32) := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 0 0) (by simp)
  have a1 := hs (.r1, .frame 88) (by simp)
  have a2 := hs (.r2, .caller 5 0) (by simp)
  change u.gpr .r0 = L.out + 0#32 at a0
  change u.gpr .r2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

def mulStepWr (L : Lay) : List Region := slots L :: mulWr L

theorem mul_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith mulAddArgs "vg_ed25519_scalar_mul_add" VG.Impl.Ed25519.Arm.scalarMulAdd) s
      fun t => Ctx L g m₀ t ∧ Frame (mulStepWr L) s.mem t.mem ∧
        Spec.Ed25519.bytesAt t.mem (State.addr L.out + 32) 32 =
          Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32)
            (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32)
            (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 24) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)])
    (stack := [.caller 5 0]) (by decide) (by simp [Whole.valid]) (by decide)
    (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hf, hs, hst⟩ => ?_)
  have a0 := hs (.r0, .caller 0 32) (by simp)
  have a1 := hs (.r1, .frame 88) (by simp)
  have a2 := hs (.r2, .frame 120) (by simp)
  have a3 := hs (.r3, .frame 24) (by simp)
  have a4 := hst 0 (by decide)
  change stackArg u 0 = L.scr + 0#32 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hft, hp⟩ => ⟨ht, ?_, ?_⟩
  · exact (hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)).trans
      (hft.mono (fun _ hr => List.mem_cons_of_mem _ hr))
  · have a := setup_field_bytes (L := L) hf (d := 88) (by decide) (by decide)
    have b := setup_field_bytes (L := L) hf (d := 120) (by decide) (by decide)
    have c := setup_field_bytes (L := L) hf (d := 24) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 88) 32 = _ at a
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 120) 32 = _ at b
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 = _ at c
    rw [a, b, c] at hp
    exact hp

end VG.Proof.Ed25519.Arm.SignCached
end

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem mul_step_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (mulStepWr L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [mulStepWr, mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (baseWithin L).sub

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 88) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa (nonceCode) s fun t => Ctx L g m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 24) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 88 (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 24) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 24) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 88) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 88) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (challengeCode) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 24) (by decide) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 88) (by decide) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 120 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 24) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 88) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 88) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 120) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (State.addr L.E + 24) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (mul_step_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (State.addr L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.bytesAt s.mem (State.addr L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 248))).symm

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (body) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.Arm.SignCached
