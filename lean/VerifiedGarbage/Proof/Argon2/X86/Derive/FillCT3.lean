import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT2
import VerifiedGarbage.Proof.Argon2.IterationsIndices

/-!
# Argon2 on x86 (32-bit): the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- A block's reference, in two runs whose references from it on agree. -/
theorem ref_same (p : Spec.Argon2.Params) (pass lane slice i count : Nat) (X₁ X₂ : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (h : (Proof.Argon2.segment p pass lane slice i (count + 1) X₁).indices =
      (Proof.Argon2.segment p pass lane slice i (count + 1) X₂).indices) :
    Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₁.memory) =
      Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₂.memory) := by
  cases hind : Spec.Argon2.independent p pass slice
  · exact Proof.Argon2.segment_first_reference p pass lane slice i count X₁ X₂ active h hind
  · unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

/-- The words of the locals a lane's state fixes. -/
abbrev wsL : List Nat := [72, 76, 80, 92, 96, 100, 132]

theorem slotsOkL : VG.X86.Taint.SlotsOk (τB [(0, 72, 12), (0, 92, 12), (0, 132, 4)]) := by
  intro x hx
  simp only [τB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : LS s₀₁ st₁ pass slice lane s₁) (h₂ : LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ wsL, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pass.trans h₂.pass.symm
  · exact h₁.lane.trans h₂.lane.symm
  · exact h₁.slice.trans h₂.slice.symm
  · exact (h₁.fb.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.fb.pr.laneLen.symm
  · exact (h₁.fb.pr.stride.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans h₂.fb.pr.stride.symm
  · exact (h₁.fb.pr.segLen.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.fb.pr.segLen.symm
  · exact (h₁.fb.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans
      h₂.fb.pr.divisor.symm

/-- `segmentStart` leaks the same trace in two runs at the same lane. -/
theorem segmentStart_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segmentStart fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.segmentStart
  refine RelCT.seq (T.leaf wsL [(0, 72, 12), (0, 92, 12), (0, 132, 4)] [] slotsOkL (by decide)
      (fun s₁ s₂ h₁ h₂ => ⟨h₁.fb.inv, h₂.fb.inv, T.wordsL h₁ h₂, by simp⟩) ⟨_, by taint_decide⟩
      (fun s h => segStartBlk_ok T.hp₁ h hpass hs) (fun s h => segStartBlk_ok T.hp₂ h hpass hs)) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.2, h₂.2.2])
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1.fb.inv, h.2.1.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : i < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane i c X₁ s₁ ∧ FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.X86.Derive.fillBlock
        (.block (Impl.Argon2.X86.Derive.advance indexOff (Impl.Argon2.X86.Derive.fr segLenOff))))
      fun v₁ v₂ => (FS s₀₁ pass slice lane (i + 1) (ctrNext (prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i X₁) v₁ ∧
          v₁.cf = some (decide (i + 1 < (prm s₀₁).segmentLen))) ∧
        (FS s₀₂ pass slice lane (i + 1) (ctrNext (prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₂) pass slice lane i X₂) v₂ ∧
          v₂.cf = some (decide (i + 1 < (prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine HPrime.rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafF [] (fun s₁ s₂ h => by
      have h₂ := h.2
      rw [← pe] at h₂
      exact ⟨⟨_, _, _, _, _, h.1.w, h₂.w⟩, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.X86.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.X86.Derive.segment
  refine RelCT.seq (HPrime.rel_wp (T.segmentStart_rel hpass hs)
    (fun s h => segmentStart_ok T.hp₁ h hpass hs) (fun s h => segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => segCmp_ok T.hp₁ h hS) (fun s h => segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => by
      show s₁.cf = s₂.cf
      rw [h.1.2, h.2.2, hL, hL₂]) ?_ ((RelCT.nil fun _ _ _ => trivial))
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      FS s₀₁ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      FS s₀₂ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      rw [show isa.eval .b s₁ = s₁.cf from rfl, c₁, hL] at e
      simpa using e
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega] at hidx
    have href := ref_same (prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega, segment_snoc, show S + (i - S) = i by omega]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
    have e : i + 1 < L := by
      rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
      simpa using hc
    exact ⟨L - (i + 1), by omega, i + 1, rfl, by omega, e, _, g₁, g₂, hidx⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ X₁ pass slice l s₁ ∧ LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.X86.Derive.segment
        (.block (Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff 7)))))
      fun v₁ v₂ => (LS s₀₁ (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ v₁.cf = some (decide (l + 1 < lanesN s₀₁))) ∧
        (LS s₀₂ (Proof.Argon2.segment (prm s₀₂) pass l slice 0 (prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          v₂.cf = some (decide (l + 1 < lanesN s₀₂))) := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact HPrime.rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => segment_ok T.hp₁ h hpass hs hl) (fun s h => segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => laneStep_ok T.hp₁ h hpass hs hl) (fun s h => laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ Y₁ pass slice s₁ ∧ SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.X86.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.lanesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (setLocal_ok T.hp₂ h.fb (d := laneOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : lanesN s₀₁ = N at hind hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      LS s₀₂ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ X₁ pass j s₁ ∧ SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.X86.Derive.lanesLoop (.block (Impl.Argon2.X86.Derive.advance sliceOff (.imm 4))))
      fun v₁ v₂ => (SS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          v₁.cf = some (decide (j + 1 < 4))) ∧
        (SS s₀₂ (Proof.Argon2.lanes (prm s₀₂) pass j 0 (lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          v₂.cf = some (decide (j + 1 < 4))) :=
  HPrime.rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => lanes_ok T.hp₁ h hpass hj) (fun s h => lanes_ok T.hp₂ h hpass hj)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => sliceStep_ok T.hp₁ h hpass hj) (fun s h => sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ Z₁ pass s₁ ∧ PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.X86.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.slicesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₁ Z₁ pass 0 t))
    (fun s h => (setLocal_ok T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) 0).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      SS s₀₁ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      SS s₀₂ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) (Proof.Argon2.slices (prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega] at hidx
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : j + 1 < 4 := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  refine ⟨4 - (j + 1), by omega, j + 1, rfl, e, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ X₁ k s₁ ∧ PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.X86.Derive.slicesLoop
        (.block (Impl.Argon2.X86.Derive.advance passOff (Impl.Argon2.X86.Derive.fr (argOff 5)))))
      fun v₁ v₂ => (PS s₀₁ (Spec.Argon2.fillPass (prm s₀₁) X₁ k) (k + 1) v₁ ∧
          v₁.cf = some (decide (k + 1 < itersN s₀₁))) ∧
        (PS s₀₂ (Spec.Argon2.fillPass (prm s₀₂) X₂ k) (k + 1) v₂ ∧ v₂.cf = some (decide (k + 1 < itersN s₀₂))) := by
  have hk₂ : k < itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : itersN s₀₁ < 2 ^ 32 := (arg s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact HPrime.rel_wp (RelCT.seqW (T.slices_rel (by omega) hind)
    (fun s h => slices_ok T.hp₁ h (by omega)) (fun s h => slices_ok T.hp₂ h (by omega))
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => passStep_ok T.hp₁ h hk) (fun s h => passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => FB s₀₁ W₁ s₁ ∧ FB s₀₂ W₂ s₂) Impl.Argon2.X86.Derive.passesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.X86.Derive.passesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_ok T.hp₁ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₁ W₁ 0 t))
    (fun s h => (setLocal_ok T.hp₂ h (d := passOff) (by decide) (by decide) 0).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₂ W₂ 0 t)) ?_
  generalize hN : itersN s₀₁ = N at hind hp1
  have hN₂ : itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      PS s₀₁ (Proof.Argon2.iterations (prm s₀₁) 0 k W₁) k s₁ ∧
      PS s₀₂ (Proof.Argon2.iterations (prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, by omega, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (prm s₀₁) (Proof.Argon2.iterations (prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : k + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (k + 1), by omega, k + 1, rfl, e, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.X86.Derive
