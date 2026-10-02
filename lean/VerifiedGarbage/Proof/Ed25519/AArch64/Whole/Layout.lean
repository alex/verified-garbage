import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! Shared frame and call invariants for complete AArch64 Ed25519. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

def Within (r R : Region) : Prop :=
  ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : Addr) : Region := ⟨E, 256⟩
abbrev ARGS (E : Addr) : Region := ⟨E + 256, 48⟩
/-- The 16 bytes below the locals: the frame of a callee saving `x30`. -/
abbrev CK (E : Addr) : Region := below E 16

/-- The baseline memory is the state after the incoming arguments have been
saved. The body cannot write those saved arguments; its callees' frames are
below the locals. -/
structure Ctx (E : Addr) (g : Reg → BitVec 64) (v : VReg → BitVec 128)
    (m₀ : Mem) (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = FR E :: W
  sp : t.sp = E
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (v r).extractLsb' 0 64
  frame : Frame (W ++ [FR E, CK E]) m₀ t.mem

namespace Ctx
variable {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
  {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    fun r hr => (hvs r hr).trans (h.vs r hr), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

/-- `of_frame`, for a callee that may also have changed its frame. -/
theorem of_frameCK (h : Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : Frame (ws ++ [CK E]) t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    fun r hr => (hvs r hr).trans (h.vs r hr), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_append_left _ hR, hs⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨CK E, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem regs (h : Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : u.v = t.v) (hm : u.mem = t.mem) : Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), ?_, hm ▸ h.frame⟩
  intro r hr
  rw [hvs]
  exact h.vs r hr

theorem readable_frame (h : Ctx E g v m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hc⟩

theorem writable_frame (h : Ctx E g v m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]
  exact ⟨FR E, List.mem_cons_self, hc⟩
end Ctx

theorem call_ok {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : Ctx E g v m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, Ctx E g v m₀ rd wr u → Frame wr' t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.callV hv hpre hcr hcw (fun u hrd hwr hsp hf hcs _ hvs hp => ?_) hn
  refine hQ u (h.of_frame hrd hwr hsp hcs hvs hf ?_) hf hp
  intro r hr
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

/-- The callee's frame is below the locals. -/
theorem ck_frame {E : Addr} {d n : Nat} (h : d + n ≤ 304) : (CK E).Disjoint ⟨E + BitVec.ofNat 64 d, n⟩ :=
  (Offset.below_disjoint E (m := 16) (l := 304) (by decide)).sub_right (Offset.sub_base _ h)

/-- Code without frames uses no stack. -/
theorem depth_zero_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, iha h.1, ihb h.2, Nat.max_self]
  | ite _ t e iht ihe =>
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, iht h.1, ihe h.2, Nat.max_self]
  | loop b _ ih => exact ih h
  | call _ b ih => exact ih h
  | frame _ _ _ => simp [Code.noFrames] at h

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth ≤ 1 := by
  rw [depth_zero_of_noFrames h]; decide

/-- `call_ok` for a callee with at most one frame (below the locals, `CK E`). -/
theorem call_okF {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : Ctx E g v m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, Ctx E g v m₀ rd wr u → Frame (wr' ++ [CK E]) t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.callFV hv hpre hcr hcw (fun u hrd hwr hsp hf hcs hvs hp => ?_) (by omega)
  have hf' : Frame (wr' ++ [CK E]) t.mem u.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton.mp hr, h.sp]
      exact ⟨CK E, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) (by decide)⟩
  refine hQ u (h.of_frameCK hrd hwr hsp hcs hvs hf' ?_) hf' hp
  intro r hr
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

end VG.Proof.Ed25519.AArch64.Whole
