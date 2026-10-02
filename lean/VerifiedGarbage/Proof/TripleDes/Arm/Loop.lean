import VerifiedGarbage.Proof.TripleDes.Arm.RoundStep
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : BitVec 32) (direction : Direction) (j : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (8 * (if direction = .encrypt then j else 15 - j))

def readKey (m : Mem) (ptr : BitVec 32) : BitVec 64 :=
  m.readW (wordAddr ptr 1) 32 ++ m.readW (wordAddr ptr 0) 32

theorem readKey_frame {m m' : Mem} {ptr : BitVec 32} {regions : List Region}
    (hf : Frame regions m m')
    (sep : ∀ j < 2, ∀ r ∈ regions, (⟨wordAddr ptr j, 4⟩ : Region).Disjoint r) :
    readKey m' ptr = readKey m ptr := by
  exact congrArg₂ (fun hi lo : BitVec 32 => hi ++ lo)
    (hf.readW (a := wordAddr ptr 1) (w := 32) (r := ⟨wordAddr ptr 1, 4⟩)
      (Region.contains_self _ _) (sep 1 (by decide)) (by decide))
    (hf.readW (a := wordAddr ptr 0) (w := 32) (r := ⟨wordAddr ptr 0, 4⟩)
      (Region.contains_self _ _) (sep 0 (by decide)) (by decide))

theorem keyAddr_step (base : BitVec 32) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then keyAddr base direction j + 8
      else keyAddr base direction j - 8) = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

def endPointer (base : BitVec 32) (d : Direction) : BitVec 32 :=
  if d = .encrypt then base + 128 else base - 8

theorem keyAddr_end (base : BitVec 32) (d : Direction) :
    (if d = .encrypt then keyAddr base d 15 + 8 else keyAddr base d 15 - 8) = endPointer base d := by
  cases d <;> simp only [endPointer, keyAddr, reduceCtorEq, ite_true, ite_false, Nat.reduceSub, Nat.reduceMul]
  · change base + BitVec.ofNat 32 120 + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 128
    rw [Offset.add_ofNat_add_ofNat]
  · rw [BitVec.add_zero]

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r10 = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .r11 = (roundPrefix keys direction (16 - n) v).2
  counter : s.gpr .r9 = BitVec.ofNat 32 n
  pointer : s.gpr .r0 = keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).1
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).2
  counter : s.gpr .r9 = 0
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .r2 (by decide)]
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .r2 (by decide)) (hs.regs .r2 (by decide)) hs.rd hs.wr
  have hreadS : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) t) 4 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : ∀ t < 2, (⟨wordAddr (s.gpr .r0) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer, hwork]; exact hsep _ hj
  have hk : (keyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (readKey s.mem (s.gpr .r0)).setWidth 48 = _
    rw [hs.pointer]
    have hmem := readKey_frame hs.frame (ptr := keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, regs, frame⟩ :=
    roundStep_ok direction s _ _ (keyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r10 = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r11 = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : Frame [spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, by
        rw [ptr, hs.pointer]
        exact keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := LoopPost keys direction base origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.Arm
