import VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad

/-! Point accumulation changes the field workspace and its table pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev accClob : List Reg := .r12 :: clob
structure AccKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest accClob s t
  frame : Frame [FA ACC b] s.mem t.mem

theorem AccKeep.ctx {b : BitVec 32} {s t : State} (h : AccKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem AccKeep.trans {b : BitVec 32} {s t u : State} (h : AccKeep b s t) (k : AccKeep b t u) :
    AccKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem AccKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem AccKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hws : ∀ r ∈ ws, r ∈ accClob) (hm : t.mem = s.mem) : AccKeep b s t :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem AccKeep.of_table {b : BitVec 32} {s t : State} {o n : Nat} (h : TableKeep b o n s t)
    (ho : 64 ≤ o) (hn : o + n ≤ 1600) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.high {b : BitVec 32} {s t : State} (h : TableKeep b 64 256 s t)
    (i : Slot) (hi : 4 ≤ i.val) :
    VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i :=
  congrArg VG.Proof.X25519.toFe (val16_congr (h.slot (by decide) i
    (.inr (by simp only [offset]; omega))))

theorem point_congr {e f : Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : point e x y z t = point f x y z t := by
  simp only [point, hx, hy, hz, ht]

theorem savePoint_d (e : Env) : evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : Env) : evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : Env) : evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : Env) :
    point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : Env) :
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

end VG.Proof.Ed25519.Arm
