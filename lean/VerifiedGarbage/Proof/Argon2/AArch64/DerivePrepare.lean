import VerifiedGarbage.Proof.Argon2.AArch64.DeriveSetup
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveNormalizeArgs

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedOffsets : List Nat := [192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .x19, 192⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : SetupDone s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  normalized : ∀ d ∈ normalizedOffsets, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : Prepared s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : ∀ d ∈ 248 :: normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ normalizedOffsets, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepareLocal s (Prepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (normalizeArgs_ok normalizedOffsets a (by decide)
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .x19 (by decide)).trans setup.bp,
    normalized.sp.trans setup.sp,
    (normalized.regs .x24 (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ arguments, ∀ d ∈ normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold normalizedWord
    have afterFrame : ∀ d ∈ normalizedOffsets, 192 ≤ d := by decide
    have bound : ∀ d ∈ normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.AArch64.Derive
