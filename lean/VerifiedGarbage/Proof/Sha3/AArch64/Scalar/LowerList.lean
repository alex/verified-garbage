import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.LowerMem
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

structure FileRel (p : Addr) (f : File) (s : VG.AArch64.State) : Prop where
  regs : ∀ r, s.gpr r = f.regs r
  slots : ∀ k < 2, s.mem.readW (p + BitVec.ofNat 64 (lowerSpillOffset k)) 64 = f.slots k
  ptr : vdword (s.v .v31) 0 = p

def spillRegion (p : Addr) : Region := { base := p + BitVec.ofNat 64 96, len := 16 }

def SlotsWritable (p : Addr) (s : VG.AArch64.State) : Prop :=
  ∀ k < 2, InRegions s.wr (p + BitVec.ofNat 64 (lowerSpillOffset k)) 8

/-- Every lowered operation realizes the abstract file step, including its
spill slots, while framing all memory outside the pair. -/
theorem step_lower_ok (op : ScalarOp) (hgood : Good op) (p : Addr)
    (f : File) (s : VG.AArch64.State) (hr : FileRel p f s) (hw : SlotsWritable p s) :
    ∃ s', runBlock isa (lower op) s = some s' ∧ FileRel p (step f op) s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [spillRegion p] s.mem s'.mem ∧
      (∀ v, v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  cases op with
  | spill k a =>
    obtain ⟨hk, ha⟩ := hgood
    obtain ⟨s', hs, hg, hm, hrd, hwr, hsp, hv⟩ :=
      spill_lower_ok s p k a hk ha hr.ptr (hw k hk)
    refine ⟨s', hs, ⟨?_, ?_, ?_⟩, hrd, hwr, hsp, ?_, fun v h28 _ => hv v h28⟩
    · intro r; exact (hg r).trans (hr.regs r)
    · intro j hj
      rw [hm]
      simp only [step]
      by_cases hjk : j = k
      · subst j
        simp only [eq_self, ite_true, Mem.readW_writeW_self64, hr.regs]
      · have sep : Mem.Sep (p + BitVec.ofNat 64 (lowerSpillOffset j)) 8 (p + BitVec.ofNat 64 (lowerSpillOffset k)) 8 :=
          Offset.sep p (by simp only [lowerSpillOffset]; omega)
            (by simp only [lowerSpillOffset]; omega) (by simp only [lowerSpillOffset]; omega)
        rw [Mem.readW_writeW_sep sep (by decide)]
        simp only [ite_eq_right hjk, hr.slots j hj]
    · rw [hv .v31 (by decide)]; exact hr.ptr
    · rw [hm]
      have hc := Offset.contains_base (p + BitVec.ofNat 64 96) (by omega : 8 * k + 8 ≤ 16)
        (by omega : 8 * k < 2 ^ 64)
      rw [Offset.add_add] at hc
      exact (Frame.refl [spillRegion p] s.mem).writeW (by simp [spillRegion]) _ hc
  | reload d k =>
    obtain ⟨hk, hd⟩ := hgood
    have hi : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (lowerSpillOffset k)) 8 := by
      obtain ⟨r, hrw, hc⟩ := hw k hk
      exact ⟨r, List.mem_append.mpr (.inr hrw), hc⟩
    obtain ⟨s', hs, hg, hm, hrd, hwr, hsp, hv⟩ :=
      reload_lower_ok s p k d hk hd hr.ptr hi
    refine ⟨s', hs, ⟨?_, ?_, ?_⟩, hrd, hwr, hsp, ?_, fun v h28 _ => hv v h28⟩
    · intro r
      rw [hg r]
      simp only [step, File.write, hr.slots k hk, hr.regs]
    · intro j hj; rw [hm]; exact hr.slots j hj
    · rw [hv .v31 (by decide)]; exact hr.ptr
    · rw [hm]; exact Frame.refl _ _
  | bicRor _ _ _ _ => exact False.elim hgood
  | _ =>
      obtain ⟨s', hs, hg, hm, hrd, hwr, hsp, hv⟩ :=
        reg_lower_ok _ hgood (by intro k r h; cases h) (by intro r k h; cases h) f s hr.regs
      refine ⟨s', hs, ⟨hg, ?_, ?_⟩, hrd, hwr, hsp, ?_, fun v _ h29 => hv v h29⟩
      · intro j hj; rw [hm]; exact hr.slots j hj
      · rw [hv .v31 (by decide)]; exact hr.ptr
      · rw [hm]; exact Frame.refl _ _

private theorem block_append (xs ys : List Instr) (s : VG.AArch64.State) :
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    change (isa.exec x s).bind (fun s' => runBlock isa (xs ++ ys) s') =
      ((isa.exec x s).bind (runBlock isa xs)).bind (runBlock isa ys)
    rw [Option.bind_assoc]
    exact congrArg (Option.bind (isa.exec x s)) (funext fun s' => ih s')

/-- A whole portable operation list runs with the same file semantics. -/
theorem list_lower_ok (ops : List ScalarOp) (hgood : ∀ op ∈ ops, Good op) (p : Addr)
    (f : File) (s : VG.AArch64.State) (hr : FileRel p f s) (hw : SlotsWritable p s) :
    ∃ s', runBlock isa (ops.flatMap lower) s = some s' ∧ FileRel p (run ops f) s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [spillRegion p] s.mem s'.mem ∧
      (∀ v, v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  induction ops generalizing f s with
  | nil => exact ⟨s, rfl, hr, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩
  | cons op ops ih =>
    obtain ⟨s₁, hs₁, hr₁, hrd₁, hwr₁, hsp₁, hframe₁, hv₁⟩ :=
      step_lower_ok op (hgood op (List.mem_cons_self ..)) p f s hr hw
    have hw₁ : SlotsWritable p s₁ := by
      intro k hk; rw [hwr₁]; exact hw k hk
    obtain ⟨s₂, hs₂, hr₂, hrd₂, hwr₂, hsp₂, hframe₂, hv₂⟩ :=
      ih (fun op ho => hgood op (List.mem_cons_of_mem _ ho)) (step f op) s₁ hr₁ hw₁
    refine ⟨s₂, ?_, hr₂, hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
      hframe₁.trans hframe₂, fun v h28 h29 => (hv₂ v h28 h29).trans (hv₁ v h28 h29)⟩
    simp only [List.flatMap_cons, block_append, hs₁, Option.bind_some, hs₂]

end VG.Proof.Sha3.AArch64.Scalar
