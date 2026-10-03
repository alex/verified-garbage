import VerifiedGarbage.Proof.TripleDes.AArch64.WordState

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  baseReg : s.gpr .x0 = base
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .x2 = s.gpr .x2)
    (hkey : t.gpr .x0 = s.gpr .x0) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, hkey.trans hs.baseReg, ?_, ?_, ?_⟩
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
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : Stable s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) (hs.regs .x2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass c d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t) := by
  have hptr : s.gpr .x0 + BitVec.ofNat 64 (passOffset c d) =
      keyAddr (componentBase base c) d 0 := by
    rw [hready.baseReg]
    exact passPointer base c d
  apply WP.mono (pass_ok c hc (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr
    (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .x2 (by decide)) (ht.regs .x0 (by decide)) ht.rd ht.wr ht.frame,
    ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩

end VG.Proof.TripleDes.AArch64
