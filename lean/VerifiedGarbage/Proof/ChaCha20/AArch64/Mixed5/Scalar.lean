import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64 (load finish addWord wreg)
open VG.Proof.ChaCha20.AArch64

/-- Reuse the scalar load proof with the stream caller's permitted regions. -/
theorem scalarLoad_ok (s : State) (hp : Pre s) :
    WP isa (.block load) s fun u =>
      Holds (V s) u ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r, ¬ Words r → u.gpr r = s.gpr r) := by
  have hi : LI s 0 s := ⟨fun _ _ h => by omega, rfl,rfl,rfl,fun _ _ => rfl⟩
  have hl : WP isa (.block load) s (LI s 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s) (fun k u hk h => load_step hp hk h)
      16 (Nat.le_refl _) s hi
  exact hl.mono fun _ h => ⟨fun k hk => h.loaded k hk hk,h.mem,h.rd,h.wr,h.keep⟩

/-- Feed forward and serialize the scalar block into the existing scratch. -/
theorem scalarFinish_ok (s : State) (hp : Pre s) {R : CState} (hh : Holds R s) :
    WP isa (.block finish) s fun u =>
      (∀ k (hk : k < 16), u.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * k)) 32 =
        R[k] + (V s)[k]) ∧ Frame [⟨s.gpr .x1,64⟩] s.mem u.mem ∧
      (∀ r, ¬ Words r → u.gpr r = s.gpr r) := by
  rw [finish_split, WP.block_append_iff, WP.block_append_iff]
  refine (first_ok hp hh rfl rfl rfl (fun _ _ => rfl)).mono fun a ha => ?_
  refine (wp_range_flatMap (M := isa) (FI s R s) (fun i u hi h => add_step hp hi h)
    15 (Nat.le_refl _) a ha).mono fun b hb => ?_
  exact (last_ok hp hb).mono fun _ ⟨ho,hk,hf⟩ => ⟨ho,hf,hk⟩

/-- Scalar instructions retain every vector, including the four NEON states. -/
theorem keeps_vectors {is : List Instr} (hv : ∀ i ∈ is, vdstOf i = none)
    {s : State} {Q : State → Prop} (hp : WP isa (.block is) s Q) :
    WP isa (.block is) s fun u => Q u ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain ⟨t,u,he,hq⟩ := hp
  refine ⟨t,u,he,hq,funext fun r => Exec.vec (fun i hi => by simp [hv i hi]) he,Exec.sp he,(Exec.regions he rfl).1,(Exec.regions he rfl).2.1⟩

end VG.Proof.ChaCha20.AArch64.Mixed5
