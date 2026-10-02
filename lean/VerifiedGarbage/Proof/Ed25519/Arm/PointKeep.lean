import VerifiedGarbage.Proof.Ed25519.Arm.MulInput
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeKeep

/-! Point engines preserve register saves, the output pointer, and
the three packed points reserved for verification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev pointRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 52, 7692⟩]

structure PointKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (pointRegions b) s.mem t.mem

theorem PointKeep.refl (b : BitVec 32) (s : State) : PointKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem PointKeep.ctx {b : BitVec 32} {s t : State} (h : PointKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem PointKeep.trans {b : BitVec 32} {s t u : State} (h : PointKeep b s t) (k : PointKeep b t u) :
    PointKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem PointKeep.of_mul {b : BitVec 32} {s t : State} (h : MulKeep b 1600 6144 s t) : PointKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  all_goals exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ (by decide) (by decide)⟩
theorem PointKeep.of_ikeep {b : BitVec 32} {s t : State} (h : IKeep b s t) : PointKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩⟩
theorem PointKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : PointKeep b s t :=
  PointKeep.of_ikeep (IKeep.of_keep h)
theorem PointKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 52 ≤ o) (hn : o + n ≤ 7744) :
    PointKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem PointKeep.word {b : BitVec 32} {s t : State} (h : PointKeep b s t)
    (d : Nat) (hd : d = 48 ∨ 7744 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem PointKeep.table {b : BitVec 32} {s t : State} (h : PointKeep b s t) {d : Nat}
    (hd : 7744 ≤ d) (hn : d + 128 ≤ 8192) : tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
