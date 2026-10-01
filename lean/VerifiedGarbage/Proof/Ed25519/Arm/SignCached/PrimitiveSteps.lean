import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashFrame
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Reduce
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.MulAdd
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached

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
