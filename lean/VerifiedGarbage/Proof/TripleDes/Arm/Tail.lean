import VerifiedGarbage.Proof.TripleDes.Arm.Store
import VerifiedGarbage.Proof.TripleDes.Arm.Head

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

structure TailPost (original origin : State) (d : Direction) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (origin.gpr .r1)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  pointer : s.gpr .r0 = (if d = .encrypt then origin.gpr .r0 - 384 else origin.gpr .r0 + 8)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨State.addr (origin.gpr .r1), 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (d : Direction) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hsavedRead : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4)
    (hsep : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)) :
    WP isa (.block (blockStore d ++ blockRestore)) s (TailPost original s d x) := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, mem₁, ptr₁, rd₁, wr₁, sp₁, reg₁⟩ := blockStore_ok d s
    ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right dataFit hwrite
  rw [VG.Proof.TripleDes.halves_append] at mem₁
  have regs₁ : ∀ q ∈ roundStepKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have incl : ∀ q ∈ roundStepKept, q ∈ loadKept ∧ q ≠ .r0 := by decide
    exact reg₁ q (incl q hq).1 (incl q hq).2
  have frame₁ : Frame [⟨State.addr (s.gpr .r1), 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .r2 (by decide)]
    have sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i), 4⟩ (saveRegion s) :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₁.readW (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (hsep.sub_right sub).symm)
      (by decide)
    exact mem.trans (hsaved i hi)
  have reads₁ : ∀ i < 9, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [rd₁, wr₁, regs₁ .r2 (by decide)]; exact hsavedRead
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁
    (by rw [regs₁ .r2 (by decide)]; exact scratchFit) reads₁)
  intro s₂ hs₂
  refine ⟨?_, hs₂.saved, ?_, hs₂.keep.rd.trans rd₁, hs₂.keep.wr.trans wr₁,
    hs₂.sp.trans sp₁, ?_, ?_⟩
  · rw [hs₂.keep.mem, mem₁]
    exact blockAt_writeW s.mem _ _
  · exact (hs₂.keep.reg .r0 (by decide)).trans ptr₁
  · intro q hq
    have unused : ∀ q ∈ roundStepKept, q ∉ savedRegs := by decide
    exact (hs₂.keep.reg q (unused q hq)).trans (regs₁ q hq)
  · rw [hs₂.keep.mem]; exact frame₁

end VG.Proof.TripleDes.Arm
