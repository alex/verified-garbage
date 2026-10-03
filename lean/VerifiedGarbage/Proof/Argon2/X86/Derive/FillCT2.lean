import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1

/-!
# Argon2 on x86 (32-bit): a block of the filling loops, in two runs

`fillBlock_rel`: one block's trace depends only on its position and on the
reference block's index, which the leakage permits (`Spec.Argon2.references`):
the reference is computed from the random word in the locals (`reference_rel`),
G is called on the previous and the reference blocks (`fillCompress_rel`), and
its output is written to the current block (`fillWrite_rel`), whose address the
runs agree on.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_add wp_addi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off refLaneOff tmpOff curOff)

/-- Two runs, from any of a family of states each. -/
theorem RelCT.exists₂ {α β : Sort _} {A : α → State → Prop} {B : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a b, RelCT isa (fun s₁ s₂ => A a s₁ ∧ B b s₂) c Q) :
    RelCT isa (fun s₁ s₂ => (∃ a, A a s₁) ∧ ∃ b, B b s₂) c Q :=
  fun _ _ _ _ _ _ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ e₁ e₂ => h a b _ _ _ _ _ _ ⟨ha, hb⟩ e₁ e₂

/-- The slots of the words `ws0` and `ex`. -/
abbrev slx (ex : List Nat) : List (Nat × Nat × Nat) := sl0 ++ ex.map fun d => (0, d, 4)

theorem slotsOkX {ex : List Nat} (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144) (rs : List Reg) :
    VG.X86.Taint.SlotsOk (τB (slx ex) rs) := by
  intro x hx
  simp only [τB, slx, List.append_assoc, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨d, hd, rfl⟩ | hx
  · exact slotsOk0 rs x (by simp only [τB]; exact List.mem_append_left _ hx)
  · have := hex d hd; simp [τB]; omega
  · exact slotsOk0 rs x (by simp only [τB]; exact List.mem_append_right _ hx)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- As `leafF`, with the words `ex` of the locals public too. -/
theorem leafX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check taint (τB (slx ex) rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB (slx ex) rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
  refine agreeB T.hp₁ T.hp₂ T.pb w₁.inv w₂.inv _ rs hr (slotsOkX hex rs)
    (slots_of_words (ws := ws0 ++ ex) (fun d hd => ?_) fun x hx => ?_)
  · rcases List.mem_append.mp hd with hd | hd
    · exact T.words w₁ w₂ d hd
    · exact he d hd
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h0, hj⟩ := (show ∀ x ∈ sl0, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws0 by decide) x hx
      exact ⟨h0, fun j hj' => List.mem_append_left _ (hj j hj')⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      refine ⟨rfl, fun j hj => List.mem_append_right _ ?_⟩
      have := (hex d hd).1
      rw [show 4 * ((d + j) / 4) = d by simp only at hj; omega]
      exact hd

/-! ## The reference -/

/-- `refLane` leaks the same trace in two runs at the same position. -/
theorem refLane_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.refLane fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => refLaneBlk_ok T.hp₁ h hpass hs) (fun s h => refLaneBlk_ok T.hp₂ h hpass hs) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.1, h₂.2.1])
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.fs.w, h.2.1.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (RelCT.nil fun _ _ _ => trivial)

/-- `reference` leaks the same trace in two runs at the same position. -/
theorem reference_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32}
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    RelCT isa (fun s₁ s₂ => RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.X86.Derive.reference fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.reference
  refine RelCT.seqW (T.refLane_rel hpass hs)
    (fun s h => (refLane_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (refLane_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (refStart_ok T.hp₁ h hpass hs).mono fun t ht => ht.1)
    (fun s h => (refStart_ok T.hp₂ h hpass hs).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (countBase_ok T.hp₁ h hpass hs).mono fun t ht => h.of_keep ht.1)
    (fun s h => (countBase_ok T.hp₂ h hpass hs).mono fun t ht => h.of_keep ht.1) ?_
  exact T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {P R : Nat} (ha : s.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024))
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa (.block [.mov .esi (Impl.Argon2.X86.Derive.fr tmpOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm 4096)]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 ∧ t.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) ∧
      t.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
  refine wp_ldloc hp h.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_ldarg hp (h.inv.upd u₂ (by decide)
    (by decide)) (i := 15) (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => WP.block_nil
    ⟨(((h.inv.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)).upd u₄ (by decide)
      (by decide)).upd u₅ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < lanesN s₀₁)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) {R : Nat} (hR : R < blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        lw s₀₁ s₁ tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024)) ∧
      (FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ lw s₀₂ s₂ tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024)))
      Impl.Argon2.X86.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := cell_fits T.hp₁ hl (col := (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
    (prm s₀₁).laneLen) (Nat.mod_lt _ (by omega))
  have L8₂ := laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := cell_fits T.hp₂ hl₂ (col := (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
    (prm s₀₂).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.fillCompress
  refine RelCT.seq (HPrime.rel_wp ((T.prevPointer_rel hs hi).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩)
      fun _ _ h => h)
    (G₁ := fun t => W s₀₁ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024) ∧ lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024))
    (G₂ := fun t => W s₀₂ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024) ∧ lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024))
    (fun s h => (prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)
    (fun s h => (prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_keep k, a, by rw [lw_mem k.mem]; exact h.2⟩)) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fcBlk_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fcBlk_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 4096) (by decide) (by decide) fun s₁ s₂ ⟨i₁, d₁, c₁, a₁, e₁⟩ ⟨i₂, d₂, c₂, a₂, e₂⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      lw s₀₁ s₁ curOff = lw s₀₂ s₂ curOff) Impl.Argon2.X86.Derive.fillWrite fun _ _ => True :=
  T.leafX [] [curOff] (by decide) (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : blocksN s₀₁ = (prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).1 * (prm s₀₁).laneLen +
    (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).1 * (prm s₀₂).laneLen +
    (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hl hs hi)
    (fun s h => randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₂) pass slice index ctr) st₂ t ∧
      lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    (RelCT.of_eq fun s₁ s₂ ⟨g₁, g₂⟩ => (T.reference_rel hpass hs (J1 := lw s₀₁ s₁ j1Off) (J2 := lw s₀₁ s₁ j2Off)
      (J1' := lw s₀₂ s₂ j1Off) (J2' := lw s₀₂ s₂ j2Off)).mono (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        rw [← pe] at g₂
        exact ⟨⟨g₁.1, rfl, rfl⟩, ⟨g₂.1, rfl, rfl⟩⟩) fun _ _ h => h)
    (fun s g => (reference_ok T.hp₁ ⟨g.1, rfl, rfl⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR], by rw [cur, hC]⟩)
    (fun s g => (reference_ok T.hp₂ ⟨g.1, rfl, rfl⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR₂], by rw [cur, hC₂]⟩)) ?_
  rw [show ctrNext (prm s₀₂) pass slice index ctr = ctrNext (prm s₀₁) pass slice index ctr by rw [pe]]
  refine RelCT.seq (HPrime.rel_wp (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.X86.Derive
