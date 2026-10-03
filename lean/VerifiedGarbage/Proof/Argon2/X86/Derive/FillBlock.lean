import VerifiedGarbage.Proof.Argon2.X86.Derive.FillWrite

/-!
# Argon2 on x86 (32-bit): one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

theorem FS.of_upd {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {r : Reg} {v : BitVec 32}
    (h : FS s₀ pass slice lane index ctr st s) (u : Upd s t r v) (h1 : r ≠ .esp) (h2 : r ≠ .ebp) :
    FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.upd u h1 h2) (fun d _ => lw_mem u.mem d) (by rw [u.mem]) fun _ _ => by rw [u.mem]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨scrB s₀, 4096⟩ := by
  have := outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  f.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) ∧
      blk t.mem (scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memB s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.fillCompress Impl.Argon2.X86.Derive.compressCall
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_keep k₁
  refine WP.seq (wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_mov fun s₄ u₄ => ?_
  have h₄ := h₃.of_upd u₄ (by decide) (by decide)
  refine wp_addi fun s₅ u₅ => WP.block_nil ?_
  have h₅ := h₄.of_upd u₅ (by decide) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have ax : s₅.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₅.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have dx : s₅.gpr .edx = scrP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : s₅.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  refine ccall_ok hp h₅.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
    · exact outside_call hp
  refine ⟨h₅.frame hp it f ho, fun d hd => by rw [lw_outside hp f ho hd, lw_mem m₅], ?_⟩
  rw [post, ax, sx, cell_addr hp cl, cell_addr hp hR, m₅]

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memB s₀) C) = if pass = 0 then blk s.mem (scrP s₀) 4096 else
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) := by
  unfold Impl.Argon2.X86.Derive.fillWrite
  refine WP.seq (wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_upd u₁ (by decide) (by decide)
  refine wp_addi fun s₂ u₂ => ?_
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ => wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  have h₅ := (h₃.of_upd u₄ (by decide) (by decide)).of_keep (Divide.Keep.of_fupd f₅)
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .esi = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  have di : s₅.gpr .edi = memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, lw_mem u₂.mem, lw_mem u₁.mem, hcur]
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  have hsf := hp.scr_fits
  have eP : (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 = scrB s₀ + BitVec.ofNat 64 4096 :=
    HPrime.setWidth_add (by omega)
  have Pfit : (scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega)]; omega
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  have PC : Region.Disjoint ⟨(scrP s₀ + BitVec.ofNat 32 4096).setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (cell_in_mem hC)
  have nxt : blk s.mem (scrP s₀) 4096 = ofWords fun i => sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  have old : blockAt s.mem (matrixCell (memB s₀) C) = ofWords fun i => mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  have done : ∀ (xo : Bool) (t : State), (∀ i < 256, mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (memB s₀) C) = if xo then
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) else blk s.mem (scrP s₀) 4096 :=
    fun xo t wt => by
      have e : blockAt t.mem (matrixCell (memB s₀) C) = ofWords fun i => if xo then
          sw s₀ s.mem (4096 + 4 * i) ^^^ mw s₀ s.mem (C * 1024 + 4 * i) else sw s₀ s.mem (4096 + 4 * i) := by
        rw [cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← mw, wt i hi, ite_eq_left hi, m₅, addr_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show s₅.zf = _
    rw [z₅, u₄.gpr, lw_mem u₃.mem, lw_mem u₂.mem, lw_mem u₁.mem, h.pos.pass, z, Wp.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₅.inv hC false si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₅.inv hC true si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memB s₀) j) = blockAt t₃.mem (matrixCell (memB s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  have lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem (by rw [hb]; exact curLt))) (by decide)
  refine ⟨it, Prm.of_lw h₃.pr fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h₃.pos.of_lw fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [scr_blk hp _ (by decide), blockAt_keep ft (fun r hr => ?_), ← scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end
end VG.Proof.Argon2.X86.Derive
