import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.LowerList
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

instance (op : ScalarOp) : Decidable (Good op) := by
  cases op <;> unfold Good <;> infer_instance

theorem core_good : ∀ op ∈ coreOps, Good op := by decide +kernel

theorem core_math (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds laneReg (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))
      (run coreOps f) := by
  have hm := chi_correct _ _ (rhoPi_correct _ _ (theta_correct A f h))
  simpa only [coreOps, run, List.foldl_append] using hm

/-- The concrete core agrees with the abstract file and changes only the
spill pair; the round constant is applied by the loop's separate iota step. -/
theorem core_file_ok (p : Addr) (f : File) (s : VG.AArch64.State)
    (hr : FileRel p f s) (hw : SlotsWritable p s) :
    ∃ s', runBlock isa coreInstrs s = some s' ∧ FileRel p (run coreOps f) s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [spillRegion p] s.mem s'.mem ∧
      (∀ v, v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) :=
  list_lower_ok coreOps core_good p f s hr hw

/-- A register-resident round core through chi, on the real machine. -/
theorem core_ok (A : Spec.Sha3.State) (p : Addr) (s : VG.AArch64.State)
    (hl : ∀ i : Nat, (hi : i < 25) → s.gpr (laneReg i) = A[i])
    (hp : vdword (s.v .v31) 0 = p) (hw : SlotsWritable p s) :
    ∃ s', runBlock isa coreInstrs s = some s' ∧
      (∀ i : Nat, (hi : i < 25) → s'.gpr (laneReg i) =
        (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[i]) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [spillRegion p] s.mem s'.mem ∧
      (∀ v, v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  let f : File := ⟨s.gpr, fun k => s.mem.readW (p + BitVec.ofNat 64 (lowerSpillOffset k)) 64⟩
  have hr : FileRel p f s := ⟨fun _ => rfl, fun _ _ => rfl, hp⟩
  have hmath := core_math A f hl
  obtain ⟨s', hs, hr', hrd, hwr, hsp, hf, hv⟩ := core_file_ok p f s hr hw
  exact ⟨s', hs, fun i hi => (hr'.regs (laneReg i)).trans (hmath i hi), hrd, hwr, hsp, hf, hv⟩

/-- Saved GPRs and the constant table remain unchanged because they are
outside the two temporary lane slots. -/
theorem spill_frame_readW {p : Addr} {m m' : Mem} (hf : Frame [spillRegion p] m m')
    (off : Nat) (hsep : off + 8 ≤ 96 ∨ 112 ≤ off) (hb : off + 8 ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 off) 64 = m.readW (p + BitVec.ofNat 64 off) 64 := by
  let r : Region := { base := p + BitVec.ofNat 64 off, len := 8 }
  have ha : r.Contains (p + BitVec.ofNat 64 off) 8 := by
    simp only [r, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]
  have hd : r.Disjoint (spillRegion p) :=
    Offset.disjoint p hsep hb (by decide : 96 + 16 ≤ 2 ^ 64)
  exact hf.readW ha (fun r' hr' => by
    have he : r' = spillRegion p := List.mem_singleton.mp hr'
    subst r'; exact hd) (by decide)

end VG.Proof.Sha3.AArch64.Scalar
