import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.RelCT

/-! Relational trace helpers for public workspace counters. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86

def regsTaint (rs : List Reg) : VG.X86.Taint.T := { regs := .ofList rs, flags := false }

theorem regsTaint_wf (rs : List Reg) (s : State) : VG.X86.Taint.Wf (regsTaint rs) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩

theorem regsTaint_agree {rs : List Reg} {s t : State}
    (h : ∀ r ∈ rs, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (regsTaint rs) s t :=
  ⟨⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => (by cases h)⟩,
    fun h => absurd rfl h, regsTaint_wf rs s, regsTaint_wf rs t,
    fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
    fun n _ h => (Nat.not_lt_zero n h).elim⟩

def pointTaint (o : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.edi], flags := false, lens := [0, 8192], bases := [(.edi, 1, 0)],
    slots := [(1, o, 4)] }

structure PointCTCtx (x : BitVec 32) (s : State) : Prop where
  ctx : Ctx x s
  lengths : List.Forall₂ (fun r l => l ≤ r.len) s.wr [0, 8192]
  separate : s.wr.Pairwise Region.Disjoint
  fits : ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32
  region : VG.X86.Taint.region s 1 = scR 8192 x

theorem PointCTCtx.keep {x : BitVec 32} {s t : State} (h : PointCTCtx x s)
    (he : t.gpr .edi = s.gpr .edi) (hw : t.wr = s.wr) : PointCTCtx x t :=
  ⟨h.ctx.keep he hw, hw ▸ h.lengths, hw ▸ h.separate, hw ▸ h.fits,
    (congrArg (fun wr => wr.getD 1 ⟨0, 0⟩) hw).trans h.region⟩

theorem pointTaint_wf {x : BitVec 32} {s : State} (h : PointCTCtx x s) (o : Nat) :
    VG.X86.Taint.Wf (pointTaint o) s := by
  apply VG.X86.Taint.Wf.entry rfl rfl
  refine ⟨fun _ => ⟨h.lengths, h.separate, h.fits⟩, ?_, fun _ hh => (by cases hh),
    fun hh => (by cases hh), fun _ hh => (by cases hh)⟩
  intro p hp
  simp only [pointTaint, List.mem_singleton] at hp
  subst p
  rw [h.ctx.edi, addr_zero, h.region]

theorem pointTaint_agree {x : BitVec 32} {s t : State} {o : Nat}
    (hs : PointCTCtx x s) (ht : PointCTCtx x t) (hw : s.wr = t.wr)
    (ho : o + 4 ≤ 8192) (hv : wd s.mem x o = wd t.mem x o) :
    VG.X86.Taint.Agree (pointTaint o) s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun _ => hw, pointTaint_wf hs o, pointTaint_wf ht o,
    ?_, ?_, fun h => (by cases h), fun n _ h => (Nat.not_lt_zero n h).elim⟩
  · intro r hr
    simp only [pointTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact hs.ctx.edi.trans ht.ctx.edi.symm
  · intro sl hsl
    simp only [pointTaint, List.mem_singleton] at hsl
    subst sl; exact ho
  · intro sl hsl k hlo hhi
    simp only [pointTaint, List.mem_singleton] at hsl
    subst sl
    change o ≤ k at hlo
    change k < o + 4 at hhi
    obtain ⟨j, hj, rfl⟩ : ∃ j < 4, k = o + j := ⟨k - o, by omega, by omega⟩
    simp only [VG.X86.Taint.byteAddr, hs.region, ht.region]
    have hx := hs.ctx.fit
    rw [← addr_eq (by omega : x.toNat + (o + j) < 2 ^ 32),
      addr_offset (x := x) (o := o) (d := j) (by omega),
      Mem.readW_byte s.mem _ hj, Mem.readW_byte t.mem _ hj]
    exact congrArg (BitVec.extractLsb' (8 * j) 8) hv

theorem ctWithRuns {P Q F₁ F₂ : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c Q) (hw : ∀ s t, P s t → WP isa c s (F₁ s) ∧ WP isa c t (F₂ t)) :
    RelCT isa P c (fun s t => Q s t ∧ ∃ a b, P a b ∧ F₁ a s ∧ F₂ b t) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨he, hq⟩ := h _ _ _ _ _ _ hp es et
  obtain ⟨⟨_, u, eu, hu⟩, ⟨_, v, ev, hv⟩⟩ := hw s t hp
  obtain ⟨-, rfl⟩ := Exec.det es eu
  obtain ⟨-, rfl⟩ := Exec.det et ev
  exact ⟨he, hq, s, t, hp, hu, hv⟩

theorem ctExecBlock_append {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem ctBlockAppend {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => VG.RelCT.seq hx hy _ _ _ _ _ _ hp
    (ctExecBlock_append ex) (ctExecBlock_append ey)

theorem ctTaintRegs {τ : VG.X86.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s t, P s t → VG.X86.Taint.Agree τ s t) (rs : List Reg)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c (fun s t => ∀ r ∈ rs, s.gpr r = t.gpr r) := by
  intro s t ts tt s' t' hp' es et
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨he, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hp') es et
  exact ⟨he, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.Proof.Ed25519.X86
