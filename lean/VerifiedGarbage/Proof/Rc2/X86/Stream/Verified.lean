import VerifiedGarbage.Proof.Rc2.X86.Stream.Wide
import VerifiedGarbage.Proof.Rc2.X86.Stream.InitCT
import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateCT

/-!
# Streaming RC2-CBC on x86 (32-bit): `Verified`

Untrusted: everything here is checked by Lean. `init` and the updates meet
`initContract` and `updateContract`, with their arguments only read; the
shared contracts let the code write them too (`wideInit`, `wideUpdate`),
which `Verified.narrowTo` allows, and `init_implies` and `update_implies`
take the proofs to the shared contracts.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-! ## `init` -/

def initRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 28⟩]
def initWr (s : State) : List Region := [⟨(arg s 5).setWidth 64, 144⟩, ⟨(arg s 6).setWidth 64, 576⟩]

def updateRd (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 28⟩]
def updateWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 144⟩, ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩, ⟨(arg s 6).setWidth 64, 576⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Stream.initContract, VG.Proof.Rc2.X86.Stream.wideInit,
    VG.Proof.Rc2.X86.Stream.updateContract, VG.Proof.Rc2.X86.Stream.wideUpdate,
    VG.Proof.Rc2.X86.Stream.initRd, VG.Proof.Rc2.X86.Stream.initWr,
    VG.Proof.Rc2.X86.Stream.updateRd, VG.Proof.Rc2.X86.Stream.updateWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit_pre (s : State) (h : wideInit.pre s) : initContract.pre (s.withRegions (initRd s) (initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem wideUpdate_pre (d : Spec.Rc2.Direction) (s : State) (h : (wideUpdate d).pre s) :
    (updateContract d).pre (s.withRegions (updateRd s) (updateWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target Impl.Rc2.X86.Stream.init (Spec.Rc2.cbcInitContract abi 24) := by
  have hsat := init_implies.sat_left
  have narrowSat : ∃ s, initContract.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Init.init_correct s hs) Init.init_constantTime (.refl narrowSat))
    initRd initWr wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
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

theorem update_verified (d : Spec.Rc2.Direction) :
    Verified target (Impl.Rc2.X86.Stream.update d) (Spec.Rc2.cbcUpdateContract abi d 40) := by
  have hsat := (update_implies d).sat_left
  have narrowSat : ∃ s, (updateContract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideUpdate_pre d s hs⟩
  apply Verified.of_implies _ (update_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Update.update_correct d s hs) (Update.update_constantTime d)
      (.refl narrowSat))
    updateRd updateWr (wideUpdate_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [updateRd, updateWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.encryptUpdate (Spec.Rc2.cbcEncryptUpdateContract abi 40) :=
  update_verified .encrypt

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.decryptUpdate (Spec.Rc2.cbcDecryptUpdateContract abi 40) :=
  update_verified .decrypt

end VG.Proof.Rc2.X86.Stream
