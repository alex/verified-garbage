import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Setup
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame

/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

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

theorem restore_ok (original s : State) (base : s.gpr .x24 = original.gpr .x4)
    (extra : ∀ r ∈ [.x25, .x26, .x27, .x28], s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .x4, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .x4 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .x4 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  have r840 := read 840 (by decide)
  have r848 := read 848 (by decide)
  have r856 := read 856 (by decide)
  have r864 := read 864 (by decide)
  have r872 := read 872 (by decide)
  have r888 := read 888 (by decide)
  have r880 := read 880 (by decide)
  have v840 := values .x19 840 (by decide)
  have v848 := values .x20 848 (by decide)
  have v856 := values .x21 856 (by decide)
  have v864 := values .x22 864 (by decide)
  have v872 := values .x23 872 (by decide)
  have v888 := values .x30 888 (by decide)
  have v880 := values .x24 880 (by decide)
  simp only [Mem.readW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at v840 v848 v856 v864 v872 v880 v888
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, addr,
    show (840 : Nat) % 8 = 0 ∧ 840 < 4096 * 8 from by decide,
    show (848 : Nat) % 8 = 0 ∧ 848 < 4096 * 8 from by decide,
    show (856 : Nat) % 8 = 0 ∧ 856 < 4096 * 8 from by decide,
    show (864 : Nat) % 8 = 0 ∧ 864 < 4096 * 8 from by decide,
    show (872 : Nat) % 8 = 0 ∧ 872 < 4096 * 8 from by decide,
    show (880 : Nat) % 8 = 0 ∧ 880 < 4096 * 8 from by decide,
    show (888 : Nat) % 8 = 0 ∧ 888 < 4096 * 8 from by decide,
    and_self, Nat.reduceMul, BitVec.setWidth_eq, Size.bits, Size.bytes,
    State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    base, r840, r848, r856, r864, r872, r880, r888,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false,
      v840, v848, v856, v864, v872, v880, v888]
  all_goals exact extra _ (by decide)

end VG.Proof.Argon2.AArch64.HPrime
