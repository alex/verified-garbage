import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
import VerifiedGarbage.Proof.Ed25519.X86.PointCTMul
import VerifiedGarbage.Proof.Ed25519.X86.PointFromInput

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyWr_agree {s t : State} (h : VerifyCTFacts s t) : s.wr = t.wr := by
  rw [h.left.2.1, h.right.2.1, h.args 3 (by decide)]

theorem verifyPointCtx_saved {s₀ s : State} (h : verifyLocal.pre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    PointCTCtx (arg s₀ 3) s := by
  have hp := (verify_pre h).scratch
  refine ⟨hs.ctx hp.fit hp.wr, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro r hr a ha _
    change _ + 1 ≤ 0 at ha
    omega_using [ha]
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [addr_zero, BitVec.toNat_setWidth]
    · omega_using [hp.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl

def sliceScalar (s : State) (i skip bytes : Nat) : Nat :=
  Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 skip).setWidth 64) bytes)

theorem pointFromInputPrepareCT_ok {s₀ s : State} {i skip bytes count : Nat}
    (h : verifyLocal.pre s₀) (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) (hn : bytes ≤ 64)
    (hc32 : count ≤ 32) (hsize : 8 * bytes = 16 * count) :
    WP isa (.block (inputSliceBits i skip bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ MulCTInput (arg s₀ 3) (sliceScalar s₀ i skip bytes) count t := by
  have hp := (verify_pre h).scratch
  refine WP.block_append (WP.mono (inputSliceBits_ok hp hi hs hia hn) fun a ⟨ha, ba, _⟩ => ?_)
  have ca := ha.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] ca) fun b ⟨kb, eb⟩ => ?_
  have hb := ha.ikeep hp.fit (IKeep.of_field kb)
  refine ⟨hb, verifyPointCtx_saved h hb, ?_, ?_, ?_⟩
  · have hh := decodeLE_lt (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hh
    change sliceScalar s₀ i skip bytes < 256 ^ bytes at hh
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, hsize] at hh
    exact hh
  · intro k hk
    rw [IKeep.bit (IKeep.of_field kb) ca k (by omega_using [hk, hc32]), ba k (by omega_using [hk, hsize]), scalarBit_nat]
    rfl
  · rw [eb]; rfl

theorem pointFromInput_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i skip bytes count : Nat)
    (hi : i ≤ 2) (hk : skip = 0 ∨ skip = 32) (hb : bytes = 32 ∨ bytes = 64)
    (hn : count = 16 ∨ count = 32) (hsize : 8 * bytes = 16 * count)
    (is : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (it : SlicePre t₀ 3 (arg t₀ i + BitVec.ofNat 32 skip) bytes) :
    RelCT isa (VerifySaved s₀ t₀) (pointFromInput i skip bytes count) (fun _ _ => True) := by
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (expandScalarBits bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) (fun _ _ => True) := by
    rcases hb with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
      intro s t h
      apply regsTaint_agree
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h.1, h.2]
  have prepct : RelCT isa (VerifySaved s₀ t₀)
      (.block (inputSliceBits i skip bytes ++ fieldCode [.const 16 Spec.Ed25519.d])) (fun _ _ => True) := by
    simp only [inputSliceBits, List.append_assoc]
    exact ctBlockAppend (loadSlicePointer_ct h i skip hi hk) tailct
  have prep := ctWithRuns prepct (fun _ _ hs =>
    ⟨pointFromInputPrepareCT_ok h.left is hs.1 (by omega) (by omega) (by omega) hsize,
     pointFromInputPrepareCT_ok h.right it hs.2 (by omega) (by omega) (by omega) hsize⟩)
  rw [pointFromInput]
  refine VG.RelCT.seq (prep.mono (fun _ _ h => h) ?_)
    (pointMultiply_ct (arg s₀ 3) (sliceScalar s₀ i skip bytes) (sliceScalar t₀ i skip bytes) count hn)
  intro s t ⟨_, a, b, _, hs, ht⟩
  exact ⟨hs.2, (h.args 3 (by decide)).symm ▸ ht.2,
    hs.1.wr.trans ((verifyWr_agree h).trans ht.1.wr.symm)⟩

end VG.Proof.Ed25519.X86
