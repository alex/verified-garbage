import VerifiedGarbage.Proof.Argon2.X86.Derive.CTCall

/-!
# Argon2 on x86 (32-bit): the random word, in two runs

`W`: the public words of the filling loops' locals (the parameters, the
position and the counter), which `Two.leafF` makes public for the taint
analysis, with any registers the runs agree on. The taint analysis forgets
that a sum with a memory operand is public (`column`, `blockAddr`,
`cacheWord`), so the pieces are cut there, and the runs related again from
what correctness says the registers hold. `randomSource_rel`: the random
word's trace depends only on the position.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_add wp_addi wp_addm wp_andi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- The public words of the filling loops' locals. -/
structure W (s₀ : State) (pass slice lane index ctr : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  ctr : lw s₀ s counterOff = BitVec.ofNat 32 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    (k : Divide.Keep s t) : W s₀ pass slice lane index ctr t :=
  ⟨h.inv.keep k, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [lw_mem k.mem]; exact h.ctr⟩

/-- The words `W` is about. -/
abbrev ws0 : List Nat := [72, 76, 80, 84, 88, 92, 96, 100, 132]

/-- Their slots. -/
abbrev sl0 : List (Nat × Nat × Nat) := [(0, 72, 32), (0, 132, 4)]

theorem slotsOk0 (rs : List Reg) : VG.X86.Taint.SlotsOk (τB sl0 rs) := by
  intro x hx
  simp only [τB, sl0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [τB]

theorem slotsOkE (rs : List Reg) : VG.X86.Taint.SlotsOk (τB [] rs) := by
  intro x hx
  simp only [τB, List.nil_append, List.mem_singleton] at hx
  subst hx; simp [τB]

/-- Composition, with what each run satisfies after the first part. -/
theorem RelCT.seqW {F₁ F₂ G₁ G₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c₁ fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c₁ s G₁) (w₂ : ∀ s, F₂ s → WP isa c₁ s G₂)
    (h₂ : RelCT isa (fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂) c₂ Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq c₁ c₂) Q :=
  RelCT.seq (HPrime.rel_wp h₁ w₁ w₂) h₂

/-- A branch on a condition that agrees in both runs. -/
theorem RelCT.iteF {F₁ F₂ : State → Prop} {c : Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) th Q) (he : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) el Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.ite c th el) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h.1 h.2) (ht.mono (fun _ _ h => h.1) fun _ _ h => h)
    (he.mono (fun _ _ h => h.1) fun _ _ h => h)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : W s₀₁ pass slice lane index ctr s₁)
    (h₂ : W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ ws0, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [ws0, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pos.pass.trans h₂.pos.pass.symm
  · exact h₁.pos.lane.trans h₂.pos.lane.symm
  · exact h₁.pos.slice.trans h₂.pos.slice.symm
  · exact h₁.pos.index.trans h₂.pos.index.symm
  · exact h₁.ctr.trans h₂.ctr.symm
  · exact (h₁.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans h₂.pr.laneLen.symm
  · exact (h₁.pr.stride.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans
      h₂.pr.stride.symm
  · exact (h₁.pr.segLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.pr.segLen.symm
  · exact (h₁.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans h₂.pr.divisor.symm

/-- A piece the taint analysis proves from the public words `W` and the
registers `rs`, which both runs agree on. -/
theorem leafF {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl0 rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB sl0 rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr⟩ := hag s₁ s₂ h
  exact agreeB T.hp₁ T.hp₂ T.pb w₁.inv w₂.inv sl0 rs hr (slotsOk0 rs)
    (slots_of_words (T.words w₁ w₂) (by decide))

/-- A piece the taint analysis proves from the arguments and the registers
`rs`, which both runs agree on. -/
theorem leafI {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB [] rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hr⟩ := hag s₁ s₂ h
  exact agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ [] rs hr (slotsOkE rs) (fun _ h => (List.not_mem_nil h).elim)

end Two

/-! ## Pointers -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem column_w {s : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    (hs : slice < 4) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.X86.Derive.column) s fun t => W s₀ pass slice lane index ctr t ∧
      t.gpr .ecx = BitVec.ofNat 32 (slice * (prm s₀).segmentLen + index) := by
  rw [← List.append_nil Impl.Argon2.X86.Derive.column]
  exact column_ok hp h.inv h.pr h.pos hs hi fun t _ c k => WP.block_nil ⟨h.of_keep k, c⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `prevPointer` leaks the same trace in two runs at the same position. -/
theorem prevPointer_rel {pass slice lane index ctr : Nat} (hs : slice < 4)
    (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.X86.Derive.prevPointer fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hc := Proof.Argon2.column_lt (prm s₀₁) T.hp₁.lanes_pos hs hi
  have hc₂ := Proof.Argon2.column_lt (prm s₀₂) T.hp₂.lanes_pos hs hi₂
  unfold Impl.Argon2.X86.Derive.prevPointer
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => column_w T.hp₁ h hs hi) (fun s h => column_w T.hp₂ h hs hi₂) ?_
  refine RelCT.seqW (T.leafF [.ecx] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe]⟩) ⟨_, by taint_decide⟩)
    (fun s h => (prevColumn_ok T.hp₁ h.1.inv h.1.pr hc h.2).mono fun t ⟨_, k⟩ => h.1.of_keep k)
    (fun s h => (prevColumn_ok T.hp₂ h.1.inv h.1.pr hc₂ h.2).mono fun t ⟨_, k⟩ => h.1.of_keep k) ?_
  exact T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} (hl : lane < lanesN s₀₁) (hs : slice < 4)
    (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.X86.Derive.dependentWord fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  unfold Impl.Argon2.X86.Derive.dependentWord
  refine RelCT.seq (HPrime.rel_wp (T.prevPointer_rel hs hi)
    (G₁ := fun t => W s₀₁ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024))
    (G₂ := fun t => W s₀₂ pass slice lane index ctr t ∧ t.gpr .eax = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024))
    (fun s h => (prevPointer_ok T.hp₁ h.inv h.pr h.pos hl hs hi).mono fun t ⟨a, k⟩ => ⟨h.of_keep k, a⟩)
    (fun s h => (prevPointer_ok T.hp₂ h.inv h.pr h.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ => ⟨h.of_keep k, a⟩)) ?_
  exact T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩

end Two

theorem W.of_lw {s₀ s t : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    (it : Inv s₀ t) (hl : ∀ d ∈ ws0, lw s₀ t d = lw s₀ s d) : W s₀ pass slice lane index ctr t :=
  ⟨it, Prm.of_lw h.pr fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => hl d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    (hl 88 (by decide)).trans h.ctr⟩

/-! ## The address block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before G's call in `stage x y o`. -/
theorem stageBlk_ok {s : State} (h : Inv s₀ s) (x y o : Nat) :
    WP isa (.block [.mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .eax (.reg .edx),
      .alu .add .eax (.imm (BitVec.ofNat 32 x)), .mov .esi (.reg .edx),
      .alu .add .esi (.imm (BitVec.ofNat 32 y)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm (BitVec.ofNat 32 o))]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = scrP s₀ + BitVec.ofNat 32 x ∧ t.gpr .esi = scrP s₀ + BitVec.ofNat 32 y ∧
      t.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide)
      (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
      (by decide)).upd u₇ (by decide) (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]

/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : W s₀ pass slice lane index ctr s)
    (ha : s.gpr .eax = BitVec.ofNat 32 c) :
    WP isa (.block [Impl.Argon2.X86.Derive.st counterOff .eax]) s (W s₀ pass slice lane index c) :=
  wp_stloc hp h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
    ⟨it, Prm.of_lw h.pr fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [vt, ha]⟩

/-- The first part of `cacheWord`: `eax :=` the address of word `index mod 128`'s pair. -/
theorem cacheWord1_ok {s : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    (hi : index < 2 ^ 30) :
    WP isa (.block [.mov .eax (Impl.Argon2.X86.Derive.fr indexOff), .alu .and .eax (.imm 127),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => W s₀ pass slice lane index ctr t ∧
      t.gpr .eax = scrP s₀ + BitVec.ofNat 32 (8 * (index % 128)) := by
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_add fun s₃ u₃ _ =>
    wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => ?_
  have h₅ := (((((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_upd u₄ (by simp))).of_keep
    (Divide.Keep.of_upd u₅ (by simp)))
  have a₅ : s₅.gpr .eax = BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, and127 (by omega), dbl32, dbl32, dbl32]
    congr 1; omega
  refine wp_addm h₅.inv.ebp (h₅.inv.arg_in hp (i := 15) (by decide)) fun s₆ u₆ => WP.block_nil
    ⟨h₅.of_keep (Divide.Keep.of_upd u₆ (by simp)), ?_⟩
  rw [u₆.gpr, h₅.inv.arg hp (by decide), a₅, BitVec.add_comm]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `stage x y o` leaks the same trace in two runs. -/
theorem stage_rel {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [.mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15)),
      .mov .eax (.reg .edx), .alu .add .eax (.imm (BitVec.ofNat 32 x)), .mov .esi (.reg .edx),
      .alu .add .esi (.imm (BitVec.ofNat 32 y)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm (BitVec.ofNat 32 o))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) (Impl.Argon2.X86.Derive.stage x y o) fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.stage
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) hc)
    (fun s h => stageBlk_ok T.hp₁ h x y o) (fun s h => stageBlk_ok T.hp₂ h x y o) ?_
  refine T.ccall_rel ho ho' fun s₁ s₂ ⟨i₁, d₁, a₁, e₁, c₁⟩ ⟨i₂, d₂, a₂, e₂, c₂⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₁]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₂]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32)
    (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index c s₁ ∧ W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.X86.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (input_ok T.hp₁ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1)
    (fun s h => (input_ok T.hp₂ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => (stage_ok T.hp₁ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ht => ht.1)
    (fun s h => (stage_ok T.hp₂ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ht => ht.1) ?_
  exact T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨_, by taint_decide⟩

/-- `cacheWord` leaks the same trace in two runs at the same position. -/
theorem cacheWord_rel {pass slice lane index c : Nat} (hi : index < 2 ^ 30) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index c s₁ ∧ W s₀₂ pass slice lane index c s₂)
      (.block Impl.Argon2.X86.Derive.cacheWord) fun _ _ => True := by
  unfold Impl.Argon2.X86.Derive.cacheWord
  refine RelCT.block_split (l₁ := [_, _, _, _, _, _]) (RelCT.seqW
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => cacheWord1_ok T.hp₁ h hi) (fun s h => cacheWord1_ok T.hp₂ h hi) ?_)
  exact T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have sl := segLen_lt T.hp₁
  have hlt := T.hp₁.lanes_lt
  unfold Impl.Argon2.X86.Derive.addressCache
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => cacheCheck_ok T.hp₁ h hi) (fun s h => cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2.2, h₂.2.2, h₁.1.cache.2.1, h₂.1.cache.2.1])
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => cacheFill_ok T.hp₁ h.1 hpass hl hs hi h.2.1 h.2.2)
    (fun s h => cacheFill_ok T.hp₂ h.1 hpass hl₂ hs hi₂ h.2.1 h.2.2)
    ((T.cacheWord_rel (by omega)).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
  refine RelCT.seqW (G₁ := W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.eax] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun s h => stctr_w T.hp₁ h.1.w h.2.1) (fun s h => stctr_w T.hp₂ h.1.w h.2.1) ?_
  exact T.addressCalls_rel hpass (by omega) (by omega) (by omega)

end Two

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.X86.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.X86.Derive.randomSource
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => FS s₀₁ pass slice lane index ctr st₁ t ∧
      t.zf = some (!Spec.Argon2.independent (prm s₀₁) pass slice))
    (G₂ := fun t => FS s₀₂ pass slice lane index ctr st₂ t ∧
      t.zf = some (!Spec.Argon2.independent (prm s₀₂) pass slice))
    (fun s h => (addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_keep k, z⟩)
    (fun s h => (addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_keep k, z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show s₁.zf = s₂.zf
      rw [h₁.2, h₂.2, pe])
    ((T.dependentWord_rel hl hs hi).mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hpass hl hs hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.X86.Derive
