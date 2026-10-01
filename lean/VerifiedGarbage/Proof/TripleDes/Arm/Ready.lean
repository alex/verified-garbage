import VerifiedGarbage.Proof.TripleDes.Arm.WordState

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .r2 = s.gpr .r2)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : Stable s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) (hs.regs .r2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (offset : Int)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (hptr : startPointer (s.gpr .r0) offset = keyAddr (componentBase base c) d 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass offset d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c) d) := by
  apply WP.mono (pass_ok offset ho (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr (ht.regs .r2 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.pointer⟩

end VG.Proof.TripleDes.Arm
