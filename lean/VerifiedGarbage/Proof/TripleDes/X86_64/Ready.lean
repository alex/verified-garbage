import VerifiedGarbage.Proof.TripleDes.X86_64.WordState

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  saved : s.mem.readW (savedKeyAddr s) 64 = base
  savedRead : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8
  countRead : InRegions (s.rd ++ s.wr) (countAddr s) 8
  countWrite : InRegions s.wr (countAddr s) 8
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (workRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem saved_work_disjoint (s : State) :
    (⟨savedKeyAddr s, 8⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .rdx = s.gpr .rdx)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [workRegion s] s.mem t.mem) : Ready keys base t := by
  have hsave : savedKeyAddr t = savedKeyAddr s := congrArg (· + BitVec.ofNat 64 48) hbase
  have hcount : countAddr t = countAddr s := congrArg (· + BitVec.ofNat 64 56) hbase
  have hwork : workRegion t = workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsave]
    have hmem := hf.readW (a := savedKeyAddr s) (w := 64)
      (r := ⟨savedKeyAddr s, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact saved_work_disjoint s) (by decide)
    exact hmem.trans hs.saved
  · rw [hrd, hwr, hsave]; exact hs.savedRead
  · rw [hrd, hwr, hcount]; exact hs.countRead
  · rw [hwr, hcount]; exact hs.countWrite
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : Direction) :
    base + BitVec.ofNat 64 (passOffset c d) = keyAddr (componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [passOffset, keyAddr, componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : Stable s s :=
  ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : workRegion t = workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) (hs.regs .rdx (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass c d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t) := by
  have hptr : s.mem.readW (savedKeyAddr s) 64 + BitVec.ofNat 64 (passOffset c d) =
      keyAddr (componentBase base c) d 0 := by
    rw [hready.saved]
    exact passPointer base c d
  apply WP.mono (pass_ok c hc (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr hready.savedRead hready.countRead hready.countWrite
    (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .rdx (by decide)) ht.rd ht.wr ht.frame,
    ht.rd, ht.wr, ht.regs, ht.frame⟩

end VG.Proof.TripleDes.X86_64
