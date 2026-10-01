import VerifiedGarbage.Proof.Argon2.X86_64.InitialStart
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize

/-! # H₀: finalize BLAKE2b and copy the digest into the derivation frame -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

structure Finished (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .rbp, 64⟩] s.mem t.mem

theorem finishCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r12)]) s fun t =>
      t.gpr .rsi = s.gpr .r12 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem finishOutput_ok (s : State) :
    WP isa (.block [.mov .r14 (.reg .rbp), .mov32 .rax (.imm 64)]) s fun t =>
      t.gpr .r14 = s.gpr .rbp ∧ t.gpr .rax = 64 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg]
  refine ⟨rfl, rfl, trivial, fun r hr h12 h14 => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rax := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, h14, ite_false]

theorem finish_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : Space s)
    (d : List Byte) (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64) :
    WP isa (finish (HPrime.hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbp) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) d ∧
      Finished s t := by
  unfold finish
  refine WP.seq ((finishCount_ok s).mono ?_)
  rintro a ⟨countA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have reprA : Repr b (Spec.Blake2.init b 64 0) a.mem (a.gpr .rbx) d := by
    rw [memA, ka.rbx]; exact repr
  refine WP.seq ((HPrime.finalize_ok v a _ d reprA (countA.trans count) bound
    hA.work hA.stackWork).mono ?_)
  rintro u ⟨digestU, regsU, rdU, wrU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.finalize_frame _ _ frameU⟩
  have ksu := ka.trans ku
  refine WP.seq ((finishOutput_ok u).mono ?_)
  rintro w ⟨dstW, countW, memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have outW : ∀ i < 64, InRegions w.wr (w.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [dstW, ← kw.rbp]
    rcases hW.output with ⟨r, hr, hc⟩
    exact ⟨r, hr, hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]; exact hi)⟩
  have sepW : (⟨w.gpr .rbx + 768, 64⟩ : Region).Disjoint ⟨w.gpr .r14, 64⟩ := by
    rw [dstW, ← kw.rbp]
    exact (hW.frameWork.sub_left (Region.sub_prefix (by decide : 64 ≤ 272))).symm.sub_left
      (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  refine (HPrime.copy_ok w 64 (by decide) (by decide) countW hW.work outW sepW).mono ?_
  intro t ht
  have sourceLength : (bytesAt w.mem (w.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨?_, fun r hr h12 h14 => ?_, ht.rd.trans ksw.rd, ht.wr.trans ksw.wr, ?_⟩
  · have dst : w.gpr .r14 = s.gpr .rbp := dstW.trans ksu.rbp
    rw [ht.mem]
    conv_lhs => arg 2; rw [← dst]
    have copied := HPrime.bytesAt_writeBytes w.mem (w.gpr .r14)
      (bytesAt w.mem (w.gpr .rbx + 768) 64) (by rw [sourceLength]; decide)
    rw [sourceLength] at copied
    rw [copied, memW, kw.rbx, ku.rbx]
    exact digestU
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r hrax hrcx hrdx h14).trans (ksw.regs r hr h12 h14)
  · apply Frame.trans (ksw.frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))))
    apply ht.frame.mono
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    rw [dstW, ksu.rbp]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end VG.Proof.Argon2.X86_64.Initial
