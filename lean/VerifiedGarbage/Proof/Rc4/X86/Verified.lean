import VerifiedGarbage.Proof.Rc4.X86.ConstantTime
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# RC4 on x86 (32-bit): `Verified`

`init` and `apply` meet `initC` and `applyC`, with their arguments only
read; the shared contracts let the code write them too (`wideInit`,
`wideApply`), which `Verified.narrowTo` allows.
-/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem ret_low (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt,
    Nat.shiftLeft_eq]
  have := b.isLt
  omega

/-- The registers the code writes. -/
def written : List Reg := [.eax, .ecx, .edx, .ebx, .esi, .edi, .ebp]

theorem callee_saved {s t : State} (hsp : t.gpr .esp = s.gpr .esp)
    (hbx : t.gpr .ebx = s.gpr .ebx) (hsi : t.gpr .esi = s.gpr .esi)
    (hdi : t.gpr .edi = s.gpr .edi) (hbp : t.gpr .ebp = s.gpr .ebp) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [hbx, hsi, hdi, hbp, hsp]

theorem init_correct (s : State) (hs : initC.pre s) :
    WP isa init s fun s' => abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨hrd, hwr, kc, ks, cs, ac, as, rc, rs, kfit, cfit, sfit, spfit⟩ := hs
  have hp : InitPre s :=
    { args := ⟨_, by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      key := ⟨_, by rw [hrd]; exact List.mem_cons_self, Region.contains_self _ _⟩
      ctx := ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
      scratch := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      keyFit := kfit, ctxFit := cfit, scratchFit := sfit, spFit := spfit
      keyCtx := kc, keyScratch := ks, ctxScratch := cs, argsCtx := ac, argsScratch := as }
  refine WP.mono (WP.keep written (init_ok s hp) (by lit_decide))
    fun t ⟨⟨hpost, hf, hbx, hsi, hdi, hbp⟩, hk⟩ => ⟨⟨callee_saved (hk.gpr (by decide)) hbx hsi hdi hbp, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rc, rs]
  · unfold initC
    dsimp only
    revert hpost
    cases Spec.Rc4.init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
    | ok c => intro hpost; exact ⟨by rw [ret_low, hpost.1]; rfl, hpost.2⟩
    | error e => cases e; intro hpost; rw [ret_low, hpost]; rfl

theorem apply_correct (s : State) (hs : applyC.pre s) :
    WP isa apply s fun s' => abiPreserved s s' ∧ applyC.post s s' := by
  have hp := applyPre_of hs
  obtain ⟨_, _, _, _, _, _, _, _, rc, rd, rs, _⟩ := hs
  refine WP.mono (WP.keep written (apply_ok s hp) (by lit_decide))
    fun t ⟨⟨hpost, hf, hbx, hsi, hdi, hbp⟩, hk⟩ => ⟨⟨callee_saved (hk.gpr (by decide)) hbx hsi hdi hbp, ?_⟩, hpost⟩
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [rc, rd, rs]

def initRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
def initWr (s : State) : List Region := [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩]

def applyRd (s : State) : List Region := [⟨argAddr s 0, 16⟩]
def applyWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 258⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
    ⟨(arg s 3).setWidth 64, 64⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc4.X86.initC, VG.Proof.Rc4.X86.wideInit,
    VG.Proof.Rc4.X86.applyC, VG.Proof.Rc4.X86.wideApply,
    VG.Proof.Rc4.X86.initRd, VG.Proof.Rc4.X86.initWr,
    VG.Proof.Rc4.X86.applyRd, VG.Proof.Rc4.X86.applyWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit_pre (s : State) (h : wideInit.pre s) :
    initC.pre (s.withRegions (initRd s) (initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem wideApply_pre (s : State) (h : wideApply.pre s) :
    applyC.pre (s.withRegions (applyRd s) (applyWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target init (initContract abi) := by
  have hsat := init_implies.sat_left
  have narrowSat : ∃ s, initC.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo (Verified.of_correct init_correct init_ct (.refl narrowSat))
    initRd initWr wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem apply_verified : Verified target apply (applyContract abi) := by
  have hsat := apply_implies.sat_left
  have narrowSat : ∃ s, applyC.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideApply_pre s hs⟩
  apply Verified.of_implies _ apply_implies
  refine Verified.narrowTo (Verified.of_correct apply_correct apply_ct (.refl narrowSat))
    applyRd applyWr wideApply_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyRd, applyWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

end VG.Proof.Rc4.X86
