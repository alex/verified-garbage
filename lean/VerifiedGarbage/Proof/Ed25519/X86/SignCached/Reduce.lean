import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (field L d)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame d, .frame 192, .caller 5 0])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by simp) (by simp)
  have a1 := hs.slot hL (j := 1) (by simp) (by simp)
  have a2 := hs.slot hL (j := 2) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.E + BitVec.ofNat 32 d at a0
  change Whole.slots L.E u 1 = L.E + 192 at a1
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (Whole.reduce_call hu (hashSpace hL) (by simp [Lay.outputs]) hd hd' a0 a1 a2)
    fun t ⟨ht, hft, hp⟩ => ⟨ht, primitive_frame hf hft, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt u.mem ((L.E + 192).setWidth 64) 64) at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  have ea : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide)
  rw [ea]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + 192, 64⟩)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (d := 192) (n := 64) (k := 24) (by decide) (by decide))
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86.SignCached
