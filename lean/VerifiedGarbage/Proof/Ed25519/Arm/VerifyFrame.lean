import VerifiedGarbage.Proof.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCompare

/-! Verification preserves the ABI saves and all public input headers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev verifyRegion (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 32, 8096⟩
structure VerifyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame [verifyRegion b] s.mem t.mem

theorem VerifyKeep.refl (b : BitVec 32) (s : State) : VerifyKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem VerifyKeep.ctx {b : BitVec 32} {s t : State} (h : VerifyKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem VerifyKeep.trans {b : BitVec 32} {s t u : State} (h : VerifyKeep b s t) (k : VerifyKeep b t u) :
    VerifyKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem VerifyKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 32 ≤ o) (hn : o + n ≤ 8128) :
    VerifyKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩
theorem VerifyKeep.of_point {b : BitVec 32} {s t : State} (h : PointKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 32 ≤ o) (hn : o + n ≤ 8128) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ ho hn⟩
theorem VerifyKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_point (PointKeep.of_keep h)
theorem VerifyKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_powers (PowersKeep.of_acc h) (o := 1600) (n := 0) (by decide) (by decide)
theorem VerifyKeep.of_decode {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : VerifyKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem VerifyKeep.header {b : BitVec 32} {s t : State} (h : VerifyKeep b s t)
    (d : Nat) (hd : 8128 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
