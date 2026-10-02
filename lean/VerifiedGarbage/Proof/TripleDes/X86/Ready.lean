import VerifiedGarbage.Proof.TripleDes.X86.WordState

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  schedule : scheduleArg s = base
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4
  argSeparate : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (workRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (workRegion s)
  slots : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ k < 128, ∀ t < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (keyAddr (componentBase base c) d j) t) 4
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [workRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : workRegion t = workRegion s := by unfold workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scheduleArg
    rw [hsp]
    have hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.argSeparate) (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    have hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

theorem Ready.congrFrame {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (rs : List Region) (hf : Frame rs s.mem t.mem)
    (hargs : ∀ q ∈ rs, (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint q)
    (hkeys : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ i < 2, ∀ q ∈ rs,
      (⟨wordAddr (keyAddr (componentBase base c) d j) i, 4⟩ : Region).Disjoint q) :
    Ready keys base t := by
  have hwork : workRegion t = workRegion s := by unfold workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scheduleArg
    rw [hsp]
    have hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      hargs (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    have hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (hkeys c hc d j hj)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : workRegion t = workRegion s := by unfold workRegion; rw [hs.bp]
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    hs.frame.trans hf⟩

theorem passPointer (base : BitVec 32) (c : Nat) (d : Direction) (s : State)
    (hs : scheduleArg s = base) : startAddr c d s = keyAddr (componentBase base c) d 0 := by
  cases d <;> simp only [startAddr, keyAddr, componentBase, hs, reduceCtorEq,
    ite_true, ite_false, Nat.mul_zero, Nat.sub_zero, Nat.reduceMul]
  all_goals rw [Offset.add_ofNat_add_ofNat]

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass c d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t) := by
  apply WP.mono (pass_ok c (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    (passPointer base c d s hready.schedule) hready.argRead (hready.read c hc d)
    (hready.separate c hc d) (hready.slots c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr ht.base ht.sp ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.base, ht.sp, ht.frame⟩⟩

end VG.Proof.TripleDes.X86
