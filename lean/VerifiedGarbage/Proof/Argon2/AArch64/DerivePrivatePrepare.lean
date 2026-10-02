import VerifiedGarbage.Proof.Argon2.AArch64.DeriveCopyArgs
import VerifiedGarbage.Proof.Argon2.AArch64.DerivePrepare

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def privateWrites (s : State) : List Region := [⟨s.sp, 192⟩, ⟨s.sp + 192, 80⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.sp
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.sp + 440) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  stackWords : ∀ j < 10, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (copyDestination j)) 64 =
    let w := s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64
    if j < 1 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (privateWrites s) s.mem t.mem

theorem private_prepare_local_ok (s : State) (bp : s.gpr .x19 = s.sp) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa (.seq (.block Impl.Argon2.AArch64.Derive.copyArgs) Impl.Argon2.AArch64.Derive.prepareLocal) s (PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  unfold Impl.Argon2.AArch64.Derive.copyArgs
  refine WP.seq ((copyArgs_ok (List.range 10) s bp
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold copyDestination; omega))).mono ?_)
  intro a copied
  have sp := copied.sp
  have base : a.gpr .x19 = s.sp := (copied.regs .x19 (by decide)).trans bp
  refine (prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [base] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 192 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, base]
      have bound : ∀ d ∈ 248 :: normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, base]
      have bound : ∀ d ∈ normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  have copiedValues (j : Nat) (hj : j < 10) :
      a.mem.readW (s.sp + BitVec.ofNat 64 (copyDestination j)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64 := by
    have word := copied.values j (List.mem_range.mpr hj)
    rw [sp] at word
    exact word
  refine ⟨prepared.bp.trans base, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 7 (by decide)
    change a.mem.readW (a.sp + 248) 64 = s.mem.readW (s.sp + 440) 64 at word
    rw [prepared.scratch, base]
    rw [sp] at word
    exact word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have notAx : ∀ arg ∈ arguments, arg.2 ≠ .x8 := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 1
    · have slot : ∀ j < 1, copyDestination j ∈ normalizedOffsets := by
        intro j hj
        have zero : j = 0 := by omega
        subst j
        decide
      rw [prepared.normalized _ (slot j small), base, copiedValues j hj, ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold copyDestination; omega)
        (by unfold copyDestination; omega) (by
          intro d hd
          have upper : ∀ d ∈ normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold copyDestination; omega)]
      rw [base]
      exact copiedValues j hj
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega)
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [base]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [base]
        have bounds : ∀ d ∈ normalizedOffsets, 192 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 192 + (d - 192) by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega)

end VG.Proof.Argon2.AArch64.Derive

namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem base_ok (s : State) : WP isa (.block [.addSp .x19 0]) s fun t =>
    t.gpr .x19 = s.sp ∧ Divide.Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 0 < 4096 from by decide,
    ite_true, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepare s (PrivatePrepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepare
  refine WP.seq ((base_ok s).mono ?_)
  rintro a ⟨base, kept⟩
  refine (private_prepare_local_ok a (base.trans kept.sp.symm)
    (by rw [kept.sp, kept.wr]; exact locals)
    (by rw [kept.sp, kept.rd, kept.wr]; exact read)).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans kept.sp, prepared.sp.trans kept.sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans kept.rd, prepared.wr.trans kept.wr, ?_⟩
  · rw [prepared.scratch, kept.sp, kept.mem]
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have other : ∀ arg ∈ arguments, arg.2 ∉ [Reg.x19] := by decide
    rw [kept.regs arg.2 (other arg ha)]
  · intro j hj
    rw [prepared.stackWords j hj, kept.sp, kept.mem]
  · intro r hr hb hx
    exact (prepared.regs r hr hb hx).trans (kept.regs r (by simpa only [List.mem_singleton] using hb))
  · have frame := prepared.frame
    simp only [privateWrites, kept.sp, kept.mem] at frame
    exact frame
end VG.Proof.Argon2.AArch64.Derive
