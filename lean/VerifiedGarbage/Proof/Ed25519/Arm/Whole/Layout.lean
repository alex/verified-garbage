import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! Shared frame and call invariants for complete Arm Ed25519. -/
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

def Within (r R : Region) : Prop :=
  ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : BitVec 32) : Region := ⟨State.addr E, 248⟩
abbrev ARGS (E : BitVec 32) : Region := ⟨State.addr E + 248, 24⟩

/-- The baseline memory is the state after the incoming arguments have been
saved. The body cannot write those saved arguments. -/
structure Ctx (E : BitVec 32) (g : Reg → BitVec 32)
    (m₀ : Mem) (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = FR E :: W
  sp : t.sp = E
  cs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = g r
  frame : Frame (W ++ [FR E]) m₀ t.mem

namespace Ctx
variable {E : BitVec 32} {g : Reg → BitVec 32}
  {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨FR E, List.mem_append_right _ (List.mem_singleton_self _), hf⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

theorem regs (h : Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = t.gpr r)
    (hm : u.mem = t.mem) : Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), hm ▸ h.frame⟩

theorem readable_frame (h : Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hc⟩

theorem writable_frame (h : Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]
  exact ⟨FR E, List.mem_cons_self, hc⟩
end Ctx

theorem call_ok {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : Ctx E g m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, Ctx E g m₀ rd wr u → Frame wr' t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  obtain ⟨trace,u,he,habi,hpost⟩ := hv _ hpre
  obtain ⟨hrd,hwr,_,hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd,State.withRegions_wr,State.withRegions_mem,State.callEntry_mem] at hrd hwr hf
  have he' := Exec.widen he (rd := t.rd) (wr := t.wr) (by simpa using hcr) (by simpa using hcw)
  simp only [State.withRegions_withRegions] at he'
  rw [show t.callEntry.withRegions t.rd t.wr=t.callEntry from rfl] at he'
  have hlr := habi.1 .lr (by decide)
  have hret : isa.ret t.callEntry (u.withRegions t.rd t.wr)=some (u.withRegions t.rd t.wr) := by
    simp only [State.withRegions_gpr] at hlr
    simp only [isa,ret,State.withRegions_gpr,hlr,ite_true]
  refine ⟨_,_,Exec.call (call_callEntry t) he' hret,?_⟩
  have hc : Ctx E g m₀ rd wr (u.withRegions t.rd t.wr) := by
    refine h.of_frame (u := u.withRegions t.rd t.wr) rfl rfl habi.2 ?_ hf ?_
    · intro r hr hrl
      simp only [State.withRegions_gpr]
      rw [habi.1 r hr,State.withRegions_gpr,State.callEntry_gpr _ (preserved_not_link r hr hrl)]
    · intro r hr
      rcases hw r hr with hf | ⟨R,hR,hs⟩
      · exact .inl hf.sub
      · exact .inr ⟨R,hR,hs.sub⟩
  apply hQ _ hc hf
  have eq : (u.withRegions t.rd t.wr).withRegions rd' wr'=u := by
    rw [State.withRegions_withRegions,←hrd,←hwr]
    rfl
  rw [eq]
  exact hpost

end VG.Proof.Ed25519.Arm.Whole
