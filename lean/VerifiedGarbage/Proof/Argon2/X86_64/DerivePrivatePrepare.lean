import VerifiedGarbage.Proof.Argon2.X86_64.DeriveCopyArgs
import VerifiedGarbage.Proof.Argon2.X86_64.DerivePrepare

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def privateWrites (s : State) : List Region := [⟨s.gpr .rsp, 120⟩, ⟨s.gpr .rsp + 176, 96⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 400) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  stackWords : ∀ j < 12, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (copyDestination j)) 64 =
    let w := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64
    if j < 3 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (privateWrites s) s.mem t.mem

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.gpr .rsp, 272⟩] s.wr)
    (read : ∀ j < 12, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepare s (PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  unfold Impl.Argon2.X86_64.Derive.prepare Impl.Argon2.X86_64.Derive.copyArgs
  refine WP.seq ((copyArgs_ok (List.range 12) s
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold copyDestination; omega))).mono ?_)
  intro a copied
  have sp := copied.regs .rsp (by decide)
  refine (prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [sp] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 120 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, sp]
      have bound : ∀ d ∈ 248 :: normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, sp]
      have bound : ∀ d ∈ normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans sp, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 9 (by decide)
    change a.mem.readW (a.gpr .rsp + 248) 64 = s.mem.readW (s.gpr .rsp + 400) 64 at word
    exact prepared.scratch.trans word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have notAx : ∀ arg ∈ arguments, arg.2 ≠ .rax := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 3
    · have slot : ∀ j < 3, copyDestination j ∈ normalizedOffsets := by decide
      rw [prepared.normalized _ (slot j small), copied.values j (List.mem_range.mpr hj), ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold copyDestination; omega)
        (by unfold copyDestination; omega) (by
          intro d hd
          have upper : ∀ d ∈ normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold copyDestination; omega)]
      exact copied.values j (List.mem_range.mpr hj)
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega)
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [sp]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [sp]
        have bounds : ∀ d ∈ normalizedOffsets, 176 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 176 + (d - 176) by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega)

end VG.Proof.Argon2.X86_64.Derive
