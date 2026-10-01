import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Setup
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame

/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem saved_read {m m' : Mem} (p sp : Addr)
    (frame : Frame [⟨p, 832⟩, below sp 16] m m')
    (stack : (below sp 16).Disjoint ⟨p, 16384⟩)
    (d : Nat) (lo : 832 ≤ d) (hi : d + 8 ≤ 16384) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  apply frame.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) ?_ ?_ (by decide)
  · simpa only [BitVec.add_zero] using
      Offset.contains_base (p + BitVec.ofNat 64 d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint p lo (by omega)).symm
    · exact (stack.sub_right (Offset.sub_base p hi)).symm

theorem restore_ok (original s : State) (base : s.gpr .rbx = original.gpr .r8)
    (sp : s.gpr .rsp = original.gpr .rsp)
    (readable : (⟨original.gpr .r8, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .r8 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  have r840 := read 840 (by decide)
  have r848 := read 848 (by decide)
  have r856 := read 856 (by decide)
  have r864 := read 864 (by decide)
  have r872 := read 872 (by decide)
  have r880 := read 880 (by decide)
  have v840 := values .rbp 840 (by decide)
  have v848 := values .r12 848 (by decide)
  have v856 := values .r13 856 (by decide)
  have v864 := values .r14 864 (by decide)
  have v872 := values .r15 872 (by decide)
  have v880 := values .rbx 880 (by decide)
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    base, r840, r848, r856, r864, r872, r880, v840, v848, v856, v864, v872, v880,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false, sp]

end VG.Proof.Argon2.X86_64.HPrime
