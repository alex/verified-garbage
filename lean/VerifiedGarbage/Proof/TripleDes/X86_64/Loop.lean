import VerifiedGarbage.Proof.TripleDes.X86_64.RoundStep
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

theorem keyAddr_step (base : Addr) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then keyAddr base direction j + 8
      else keyAddr base direction j - 8) = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)
  · change base + BitVec.ofNat 64 (8 * (15 - j)) - BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [Offset.add_ofNat_sub _ (by omega)]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r12 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 n
  pointer : s.gpr .rdi = keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.mem.readW (countAddr s) 64 = 0
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have haddr : countAddr s = countAddr origin := by
    simp only [countAddr, hs.regs .rdx (by decide)]
  have hwork : workRegion s = workRegion origin := by
    simp only [workRegion, hs.regs .rdx (by decide)]
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .rdx (by decide)) (hs.regs .rdx (by decide)) hs.rd hs.wr
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer]
    intro a ha hb
    apply hsep _ hj a ha
    rw [← hwork]
    exact spill_sub_work s a hb
  have hreadCountS : InRegions (s.rd ++ s.wr) (countAddr s) 8 := by
    rw [hs.rd, hs.wr, haddr]; exact hcountRead
  have hwriteCountS : InRegions s.wr (countAddr s) 8 := by
    rw [hs.wr, haddr]; exact hcountWrite
  have hk : (s.mem.readW (s.gpr .rdi) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    have hmem := hs.frame.readW (a := keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, regs, frame⟩ :=
    roundStep_ok direction s _ _ (s.mem.readW (s.gpr .rdi) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter hreadCountS hwriteCountS
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r12 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r13 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : Frame [workRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
      rw [ptr, hs.pointer, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.gpr .rdi = keyAddr base direction 0)
    (hcount : origin.mem.readW (countAddr origin) 64 = BitVec.ofNat 64 16)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := LoopPost keys direction origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hcountRead hcountWrite hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.X86_64
