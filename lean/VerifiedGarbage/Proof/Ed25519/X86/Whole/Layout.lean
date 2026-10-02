import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! Shared frame and call invariants for complete Ed25519 operations on x86. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : BitVec 32) : Region := ⟨E.setWidth 64, 256⟩
abbrev STK (E : BitVec 32) : Region := ⟨E.setWidth 64 - 24, 280⟩

theorem frame_sub (E : BitVec 32) : Region.Sub (FR E) (STK E) := by
  have h := Offset.sub_base (E.setWidth 64 - 24) (d := 24) (n := 256) (k := 280) (by decide)
  change Region.Sub ⟨E.setWidth 64 - 24 + 24, 256⟩ (STK E) at h
  rw [BitVec.sub_add_cancel] at h
  exact h

theorem below_sub_stack {E : BitVec 32} (hE : 24 ≤ E.toNat) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below E n) (STK E) := by
  have h := below_sub hn hE
  refine fun p hp => ?_
  have h' := h p hp
  simp only [below, Taint.sub_setWidth hE] at h'
  exact Region.sub_prefix (by decide : 24 ≤ 280) p h'

/-- Outer read/write regions exclude the frame. The entry arguments remain in
read-only memory above it. Secret buffers and outgoing cdecl arguments occupy
its 256 bytes; calls use at most 24 more bytes below it. -/
structure Ctx (E : BitVec 32) (g : Reg → BitVec 32) (m₀ : Mem)
    (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = FR E :: W
  esp : t.gpr .esp = E
  cs : ∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = g r
  frame : Frame (W ++ [STK E]) m₀ t.mem

namespace Ctx
variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hesp : u.gpr .esp = t.gpr .esp)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .esp → u.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨STK E, List.mem_append_right _ (List.mem_singleton_self _), fun p hp => frame_sub E p (hf p hp)⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

theorem regs (h : Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hesp : u.gpr .esp = t.gpr .esp)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .esp → u.gpr r = t.gpr r) (hm : u.mem = t.mem) :
    Ctx E g m₀ rd wr u :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), hm ▸ h.frame⟩

theorem readable_frame (h : Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨FR E, List.mem_append_right _ (List.mem_cons_self), hc⟩

theorem writable_frame (h : Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]; exact ⟨FR E, List.mem_cons_self, hc⟩

end Ctx

/-- Invoke a verified cdecl callee from the shared outgoing argument area.
The precise write frame remains available for retaining other local buffers. -/
theorem call_ok {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {t : State} (h : Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hstack : stackUse c ≤ 20)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, Ctx E g m₀ rd wr u → Frame (wr' ++ [below E 24]) t.mem u.mem →
      (∀ r, (∀ i ∈ VG.instrs c, Taint.clobbers i r = false) → u.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = u.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = u.gpr r) ∧
        k.post (t.callEntry.withRegions rd' wr') s₂) → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.call hv hsp (by rw [h.esp]; omega) hpre hcr hcw fun u hrd hwr hcs hf hg hp => ?_
  have hf' : Frame (wr' ++ [below E 24]) t.mem u.mem := by
    rw [h.esp] at hf
    exact Frame.below_mono hf (by omega) hE
  refine hQ u ⟨hrd.trans h.rd, hwr.trans h.wr, (hcs .esp (by simp [calleeSaved])).trans h.esp,
    fun r hr hn => (hcs r hr).trans (h.cs r hr hn), h.frame.trans ?_⟩ hf' hg hp
  refine Frame.sub hf' fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨STK E, List.mem_append_right _ (List.mem_singleton_self _), fun p hp => frame_sub E p (hf.sub p hp)⟩
    · exact ⟨R, List.mem_append_left _ hR, hs.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨STK E, List.mem_append_right _ (List.mem_singleton_self _), below_sub_stack hE (by decide)⟩

end VG.Proof.Ed25519.X86.Whole
