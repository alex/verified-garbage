import VerifiedGarbage.Proof.Ed25519.Arm.PointBatch
import VerifiedGarbage.Proof.Ed25519.Arm.BatchBits

/-! Frames for scalar multiplication preserve argument pointers,
register saves, and all data beyond the compact tables. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev mulRegions (b : BitVec 32) (o n : Nat) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA ACC b,
    ⟨State.addr b + BitVec.ofNat 64 o, n⟩]

structure MulKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (mulRegions b o n) s.mem t.mem

theorem MulKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : MulKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem MulKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)
theorem MulKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : MulKeep b o n s t) (k : MulKeep b o n t u) : MulKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem MulKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : MulKeep b o' n' s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))), Offset.sub _ ho hn⟩
theorem MulKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) : MulKeep b o n s t :=
  ⟨h.rest, Frame.mono h.frame (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩
theorem MulKeep.of_loop {b : BitVec 32} {o n : Nat} {s t : State}
    (h : LoopKeep b s t) : MulKeep b o n s t :=
  ⟨h.rest.mono (by decide), h.frame.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [mulRegions, List.mem_cons, true_or, or_true])⟩
theorem MulKeep.of_bits {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)⟩
theorem MulKeep.of_rest {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem MulKeep.word {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192)
    (d : Nat) (hd : d = 48 ∨ d = 52) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    have := ACC_eq
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem MulKeep.table {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192)
    (hn : o + n ≤ 8192) (hs : d + 128 ≤ o ∨ o + n ≤ d) :
    tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  have := ACC_eq
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem smallFrame_env {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64) :
    env m' b = env m b := by
  funext i
  exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)))

theorem smallFrame_lim {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hl : AllLim m b) : AllLim m' b := by
  intro i k hk
  rw [limb_frame hf (fun r hr j hj => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk]
  exact hl i k hk

end VG.Proof.Ed25519.Arm
