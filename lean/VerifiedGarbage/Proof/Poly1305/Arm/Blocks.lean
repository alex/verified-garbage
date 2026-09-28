import VerifiedGarbage.Proof.Poly1305.Arm.Regions
import VerifiedGarbage.Proof.Poly1305.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Poly1305 on 32-bit ARM: `blocks`

Untrusted: everything here is checked by Lean. After saving the registers,
storing the block pointer and count in the state, computing the limbs of `r`
and loading the accumulator as columns (`prologue_ok`), each block is
absorbed into the columns (`body_ok`); then the columns are reduced and
stored as the accumulator (`epilogue_ok`). Between blocks (`Common`), the
columns are congruent modulo `p` to the accumulator of the blocks so far.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state's address. -/
abbrev stB : Addr := State.addr (s₀.gpr .r0)
/-- The limbs of the clamped `r`, and its value. -/
abbrev Rl : Nat → Nat := rlimb s₀.mem (stB s₀)
abbrev Rn : Nat := val (Rl s₀)
/-- The accumulator on entry (if it is below `p`). -/
abbrev A0 : Nat := val (accD s₀.mem (stB s₀))
/-- The number of blocks, their region, and the first `i` of them. -/
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev blR : Region := ⟨State.addr (s₀.gpr .r1), 16 * nb s₀⟩
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (16 * i)
end

/-- The ranges of the state written once the registers are saved: `[0, 24)`
and `[56, 128)`. -/
abbrev wkL : List (Nat × Nat) := [(0, 24), (56, 72)]

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem KeepsF.sub {ws : List Reg} {F F' : List Region} {s s' : State} (h : KeepsF ws F s s')
    (hs : ∀ r ∈ F, ∃ r' ∈ F', Region.Sub r r') : KeepsF ws F' s s' :=
  ⟨h.gpr, h.frame.sub hs, h.rd, h.wr, h.sp⟩

/-- The precondition of `blocks`, by field. -/
structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0)]
  st_bl : (stR (s₀.gpr .r0)).Disjoint (blR s₀)
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  bl_fit : (s₀.gpr .r1).toNat + 16 * nb s₀ ≤ 2 ^ 32

theorem BPre.of (s : State) (h : Proof.Poly1305.blocksArm.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  keeps : KeepsF work (offR (stB s₀) wkL) s₀ s
  saved : Saved (stB s₀) s₀.gpr s.mem
  r : ∀ k < 10, rval s.mem (stB s₀) k = Rl s₀ k
  acc : ∃ D, ColsD D (stB s₀) s ∧ (∀ k < 10, D k ≤ 3564723200) ∧
    val D % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P

/-- The loop invariant, before block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## A block -/

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16 := by
  simp only [blks]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega, Poly1305.bytesAt_add]

/-- The block's value with the `0x01` byte appended. -/
theorem leNum_pad (b : List Byte) (h : b.length = 16) : leNum (b ++ [0x01]) = leNum b + 2 ^ 128 := by
  rw [Poly1305.leNum_append, h]; rfl

theorem body_eq : body = .block ([.ldr .r1 .r0 ptrOff, .dp .add .r2 .r1 (.imm 16), .str .r2 .r0 ptrOff] ++
    (absorb true ++ [.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff])) := by
  simp only [body, List.append_assoc]

theorem body_ok {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (isa.eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hfit := hp.st_fit
  have hbf := hp.bl_fit
  have hn32 : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  obtain ⟨D, hcD, hDb, hDv⟩ := hL.acc
  have hk := hL.keeps
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := hk.gpr _ (by decide)
  have hw : stR (s₀.gpr .r0) ∈ s.wr := by rw [hk.wr, hp.wr]; exact List.mem_singleton_self _
  rw [body_eq, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 124) (by decide) (by rw [hs0]; exact ea hfit (off := 124) (by omega))
    (inSt hw (off := 124) (n := 4) (by omega)) fun s₁ u₁ => ?_
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact ea hfit (off := 124) (by omega))
    (by rw [u₂.wr, u₁.wr]; exact outSt hw (off := 124) (n := 4) (by omega)) fun s₃ u₃ => ?_
  -- The state before `absorb`.
  have hptr : s₃.gpr .r1 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hL.ptr]
  have m₃ : s₃.mem = s.mem.writeW (stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1 + BitVec.ofNat 32 (16 * (i + 1))) := by
    have e : BitVec.ofNat 32 (16 * i) + 16 = BitVec.ofNat 32 (16 * (i + 1)) := by
      rw [show 16 * (i + 1) = 16 * i + 16 by ring, BitVec.ofNat_add]; rfl
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hL.ptr, BitVec.add_assoc, e]
  have f₃ : Frame (offR (stB s₀) [(124, 4)]) s.mem s₃.mem := by
    rw [m₃]; exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) le_rfl le_rfl
      (by omega) _ rfl
  have k₃ : KeepsF [.r1, .r2] (offR (stB s₀) [(124, 4)]) s s₃ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1],
      f₃, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  have hs30 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [k₃.gpr _ (by decide), hs0]
  have hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [k₃.wr]; exact hw
  have hR₃ : ∀ k < 10, rval s₃.mem (stB s₀) k = Rl s₀ k := fun k hk' => by
    rw [rval_frame' f₃ (by decide) (by decide) hk']; exact hL.r k hk'
  have hc₃ : ColsD D (stB s₀) s₃ := ⟨fun k hk' => by
      have := yr_ne k hk'
      rw [k₃.gpr _ (by simp [this.2.1, this.2.2.1])]; exact hcD.1 k hk',
    by rw [f₃.word (by decide) (by decide) (by decide)]; exact hcD.2⟩
  -- The block.
  have hbA : ∀ j < 4, State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i + 4 * j) := fun j hj => by
    rw [hptr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (a := s₀.gpr .r1) (k := 16 * i + 4 * j) (by omega)
  have hin : ∀ j < 4, InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 :=
    fun j hj => by
      rw [hbA j hj, k₃.rd, hk.rd, hp.rd]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
        contains_off (off := 16 * i + 4 * j) (n := 4) (len := 16 * nb s₀) (by omega) (by omega)⟩
  have hfr : Frame [stR (s₀.gpr .r0)] s₀.mem s₃.mem :=
    (hk.frame.trans (f₃.offR_sub (l' := wkL) (by decide) (by decide))).sub fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hp' with rfl | rfl
      · exact sub_base _ (by omega) (by omega)
      · exact sub_base _ (by omega) (by omega)
  have hmsg : msgVal s₃ = leNum (bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16) := by
    have e : ∀ j < 4, (word s₃ j).toNat =
        (s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (4 * j)) 32).toNat :=
      fun j hj => by
        simp only [word]
        rw [hbA j hj, off_add, hfr.readW (Region.contains_self _ _) (by
          simp only [List.mem_singleton, forall_eq]
          exact (hp.st_bl.sub_right (sub_base _ (by omega) (by omega))).symm) (by decide)]
    rw [leNum_bytesAt_16, msgVal, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rw [← List.append_nil [Instr.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff]]
  refine WP.append (absorb_ok hfit true (fun i hi => rlimb_lt _ _ i) hDb hs30 hw₃ hR₃ hc₃ hin)
    fun s₄ ⟨D', hc₄, hb₄, hv₄, k₄⟩ => ?_
  have hs40 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs30]
  have hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  have f₄ : Frame (offR (stB s₀) [(0, 20)]) s₃.mem s₄.mem := by rw [← accR_offR]; exact k₄.frame
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide) (by rw [hs40]; exact ea hfit (off := 20) (by omega))
    (inSt hw₄ (off := 20) (n := 4) (by omega)) fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₆ u₆ hz₆ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), hs40]; exact ea hfit (off := 20) (by omega))
    (by rw [u₆.wr, u₅.wr]; exact outSt hw₄ (off := 20) (n := 4) (by omega)) fun s₇ u₇ => WP.block_nil ?_
  -- The count.
  have hc₅ : s₅.gpr .r1 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [u₅.gpr, f₄.word (by decide) (by decide) (by decide), f₃.word (by decide) (by decide) (by decide), hL.cnt]
  have hc₆ : s₆.gpr .r1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [u₆.gpr, hc₅, show nb s₀ - i = (nb s₀ - (i + 1)) + 1 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hz : s₇.z = decide (nb s₀ - (i + 1) = 0) := by
    rw [u₇.z, hz₆, ← u₆.gpr, hc₆, ofNat_beq_zero (by omega)]
  have m₇ : s₇.mem = s₄.mem.writeW (stB s₀ + BitVec.ofNat 64 20) (BitVec.ofNat 32 (nb s₀ - (i + 1))) := by
    rw [u₇.mem, hc₆, u₆.mem, u₅.mem]
  have f₇ : Frame (offR (stB s₀) [(0, 24), (124, 4)]) s.mem s₇.mem := by
    rw [m₇]
    refine Frame.writeOff ((f₃.offR_sub (by decide) (by decide)).trans (f₄.offR_sub (by decide) (by decide)))
      (a := 0) (len := 24) (by decide) (by omega) (by omega) (by omega) _ rfl
  have k₇ : KeepsF work (offR (stB s₀) [(0, 24), (124, 4)]) s s₇ := by
    refine ⟨fun r hr => ?_, f₇, by rw [u₇.rd, u₆.rd, u₅.rd, k₄.rd, k₃.rd], by rw [u₇.wr, u₆.wr, u₅.wr, k₄.wr, k₃.wr],
      by rw [u₇.sp, u₆.sp, u₅.sp, k₄.sp, k₃.sp]⟩
    have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    have h2 : r ≠ .r2 := by rintro rfl; exact hr (by decide)
    rw [u₇.gpr, u₆.other _ h1, u₅.other _ h1, k₄.gpr _ hr, k₃.gpr _ (by simp [h1, h2])]
  have hC : Common s₀ (i + 1) s₇ := by
    refine ⟨hk.trans (k₇.sub (sub_offR _ (by decide) (by decide))), hL.saved.frame f₇ (by decide) (by decide),
      fun k hk' => by rw [rval_frame' f₇ (by decide) (by decide) hk']; exact hL.r k hk', D', ⟨fun k hk' => ?_, ?_⟩,
      hb₄, ?_⟩
    · have := yr_ne k hk'
      rw [u₇.gpr, u₆.other _ this.2.1, u₅.other _ this.2.1]; exact hc₄.1 k hk'
    · rw [m₇, readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]; exact hc₄.2
    · have h16 : (blks s₀ i).length % 16 = 0 := by simp only [blks, Poly1305.length_bytesAt]; omega
      have hl := Poly1305.length_bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16
      rw [blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block (by omega) (by omega), hv₄, hmsg,
        leNum_pad _ hl, iteT rfl, Nat.add_assoc]
      exact mod_step hDv
  by_cases hlast : i + 1 = nb s₀
  · refine .inl ⟨by rw [eval_ne, hz, hlast]; simp, hlast ▸ hC⟩
  · refine .inr ⟨by rw [eval_ne, hz]; simp; omega, by omega, { hC with ptr := ?_, cnt := ?_ }⟩
    · rw [m₇, readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
        f₄.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
    · rw [m₇, Mem.readW_writeW_self32]

/-! ## Setup -/

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The limbs of `r` and the accumulator's columns, from the state's key and accumulator. -/
theorem setupAcc_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block (setupR ++ loadAcc)) s fun s' =>
      (∀ k < 10, rval s'.mem (State.addr st) k = rlimb s.mem (State.addr st) k) ∧
      ColsD (accD s.mem (State.addr st)) (State.addr st) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(0, 20), (88, 36)]) s s' := by
  refine WP.append (setupR_ok hfit h0 hw) fun s₁ ⟨hr₁, k₁⟩ => ?_
  have f₁ : Frame (offR (State.addr st) [(88, 36)]) s.mem s₁.mem := k₁.frame
  refine WP.mono (loadAcc_ok hfit (by rw [k₁.gpr _ (by decide), h0]) (by rw [k₁.wr]; exact hw))
    fun s₂ ⟨hc₂, k₂⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [rval_frame k₂.frame hk]; exact hr₁ k hk
  · rw [← accD_frame f₁ (by decide) (by decide)]; exact hc₂
  · have k₁' : KeepsF (.r1 :: .r2 :: .r12 :: yregs) (offR (State.addr st) [(88, 36)]) s s₁ := k₁
    refine (k₁'.sub (sub_offR _ (l' := [(0, 20), (88, 36)]) (by decide) (by decide))).trans ?_
    have := k₂.sub (F' := offR (State.addr st) [(0, 20), (88, 36)]) (by
      rw [accR_offR]; exact sub_offR _ (by decide) (by decide))
    exact this

/-- Reducing the columns fully (see `reduceRegs`). -/
theorem reduce_ok {D : Nat → Nat} (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (hc : ColsD D (State.addr st) s) :
    WP isa (.block reduce) s fun s' => Cols (redL D) s' ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  rw [reduce]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide) (by rw [h0]; exact ea hfit (off := 16) (by omega))
    (inSt hw (off := 16) (n := 4) (by omega)) fun s₁ u₁ => ?_
  have hc₁ : Cols D s₁ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [u₁.other _ (yr_ne j h).2.1]; exact hc.1 j h
    · rw [show j = 9 by omega, yr9, u₁.gpr]; exact hc.2
  refine WP.mono (reduceRegs_ok (fun j hj => by have := hD j hj; omega) hc₁) fun s₂ ⟨hc₂, _, k₂⟩ =>
    ⟨hc₂, (u₁.keeps (by simp [cregs])).trans k₂⟩

end

/-! ## Prologue -/

theorem blks_zero (s₀ : State) : blks s₀ 0 = [] := by simp [blks, bytesAt]

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (saveRegs ++ [.str .r1 .r0 ptrOff, .str .r2 .r0 cntOff] ++ setupR ++ loadAcc ++
      [.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)])) s₀ fun s =>
      LInv s₀ 0 s ∧ s.z = (s₀.gpr .r2 == 0) := by
  have hfit := hp.st_fit
  have hw : stR (s₀.gpr .r0) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_singleton_self _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (saveRegs_ok hfit rfl hw) fun s₁ ⟨hsv, hf₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_
  have hw₁ : stR (s₀.gpr .r0) ∈ s₁.wr := by rw [hwr₁]; exact hw
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [hg₁]; exact ea hfit (off := 124) (by omega)) (outSt hw₁ (off := 124) (n := 4) (by omega))
    fun s₂ u₂ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₂.gpr, hg₁]; exact ea hfit (off := 20) (by omega))
    (by rw [u₂.wr]; exact outSt hw₁ (off := 20) (n := 4) (by omega)) fun s₃ u₃ => ?_
  have m₃ : s₃.mem = (s₁.mem.writeW (stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1)).writeW
      (stB s₀ + BitVec.ofNat 64 20) (s₀.gpr .r2) := by rw [u₃.mem, u₂.mem, u₂.gpr, hg₁]
  have f₁₃ : Frame (offR (stB s₀) [(20, 4), (124, 4)]) s₁.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (by decide) le_rfl le_rfl
      (by omega) _ rfl) (a := 20) (len := 4) (by decide) le_rfl le_rfl (by omega) _ rfl
  have hs₃0 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [u₃.gpr, u₂.gpr, hg₁]
  have hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  rw [← List.append_assoc setupR loadAcc]
  refine WP.append (setupAcc_ok hfit hs₃0 hw₃) fun s₄ ⟨hr₄, hc₄, k₄⟩ => ?_
  have hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs₃0]
  have hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [hs₄0]; exact ea hfit (off := 20) (by omega)) (inSt hw₄ (off := 20) (n := 4) (by omega))
    fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have f₀₁ : Frame (offR (stB s₀) [(56, 32)]) s₀.mem s₁.mem := hf₁
  have f₁₄ : Frame (offR (stB s₀) [(0, 20), (20, 4), (88, 36), (124, 4)]) s₁.mem s₄.mem :=
    (f₁₃.offR_sub (by decide) (by decide)).trans (k₄.frame.offR_sub (by decide) (by decide))
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- The key and the stored accumulator on entry.
  have f₀₃ : Frame (offR (stB s₀) [(20, 4), (56, 32), (124, 4)]) s₀.mem s₃.mem :=
    (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₃.offR_sub (by decide) (by decide))
  have hRl : rlimb s₃.mem (stB s₀) = Rl s₀ := rlimb_frame' f₀₃ (by decide) (by decide)
  have hA : accD s₃.mem (stB s₀) = accD s₀.mem (stB s₀) := accD_frame f₀₃ (by decide) (by decide)
  have hptr : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃,
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  have hcnt : s₄.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r2 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  refine ⟨⟨⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun k hk => ?_, accD s₀.mem (stB s₀), ⟨fun k hk => ?_, ?_⟩,
    fun k _ => by have := accD_lt s₀.mem (stB s₀) k; omega, by rw [blks_zero, Poly1305.absorbAll_nil]⟩, ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    rw [u₆.gpr, u₅.other _ h1, k₄.gpr _ (by
      simp only [yregs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)),
      u₃.gpr, u₂.gpr, hg₁]
  · rw [m₆]
    exact (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₄.offR_sub (by decide) (by decide))
  · rw [u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, hrd₁]
  · rw [u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, hwr₁]
  · rw [u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, hsp₁]
  · rw [m₆]; exact hsv.frame f₁₄ (by decide) (by decide)
  · rw [m₆, ← hRl]; exact hr₄ k hk
  · have := yr_ne k hk
    rw [u₆.gpr, u₅.other _ this.2.1, ← hA]; exact hc₄.1 k hk
  · rw [m₆, ← hA]; exact hc₄.2
  · rw [m₆, hptr]; simp
  · rw [m₆, hcnt]; simp [nb]
  · rw [hz, u₅.gpr, hcnt]; simp

/-! ## Epilogue -/

/-- The stores of the accumulator's first five words. -/
def accList : List (Reg × Nat × Bool) :=
  [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false), (.r1, 16, false)]

theorem epi_eq : [Instr.str .r3 .r0 0, .str .r5 .r0 4, .str .r7 .r0 8, .str .r10 .r0 12, .str .r1 .r0 16,
    .mov .r2 (.imm 0), .str .r2 .r0 20] ++ restoreRegs =
    accList.map (storeI .r0) ++ (.mov .r2 (.imm 0) :: .str .r2 .r0 20 :: restoreRegs) := rfl

theorem accList_frame (B : Addr) : accList.map (sregion B) = offR B [(0, 4), (4, 4), (8, 4), (12, 4), (16, 4)] :=
  rfl

theorem preserved_cases : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedReg i = r := by decide

/-- The accumulator's words as a number. -/
theorem val_words {L : Nat → Nat} (hL : ∀ j < 9, L j < 2 ^ 13) :
    tw0 L + 2 ^ 32 * tw1 L + 2 ^ 64 * tw2 L + 2 ^ 96 * tw3 L + 2 ^ 128 * (L 9 / 2 ^ 11) + 2 ^ 160 * 0 =
      val L := by
  rw [val_toWords hL, tw0, tw1, tw2, tw3]; omega

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block (reduce ++ toWords ++ [.str .r3 .r0 0, .str .r5 .r0 4, .str .r7 .r0 8, .str .r10 .r0 12,
      .str .r1 .r0 16, .mov .r2 (.imm 0), .str .r2 .r0 20] ++ restoreRegs)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  have hfit := hp.st_fit
  obtain ⟨D, hcD, hDb, hDv⟩ := hc.acc
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := hc.keeps.gpr _ (by decide)
  have hw : stR (s₀.gpr .r0) ∈ s.wr := by rw [hc.keeps.wr, hp.wr]; exact List.mem_singleton_self _
  have hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega
  obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
  simp only [List.append_assoc]
  refine WP.append (reduce_ok hfit hDb hs0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  refine WP.append (toWords_ok hc₁ fun j hj => hlL j (by omega)) fun s₂ ⟨e3, e5, e7, e10, e1, k₂⟩ => ?_
  have k₁₂ := k₁.trans (k₂.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cregs, yregs])
  have hs₂0 : s₂.gpr .r0 = s₀.gpr .r0 := by rw [k₁₂.gpr _ (by decide), hs0]
  have hw₂ : stR (s₀.gpr .r0) ∈ s₂.wr := by rw [k₁₂.wr]; exact hw
  rw [epi_eq]
  refine WP.append (stores_ok .r0 hfit rfl accList s₂ hs₂0 hw₂ (by decide) (by decide))
    fun s₃ ⟨hs₃, hf₃, hg₃, hrd₃, hwr₃, hsp₃⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₄.other _ (by decide), hg₃, hs₂0]; exact ea hfit (off := 20) (by omega))
    (by rw [u₄.wr, hwr₃]; exact outSt hw₂ (off := 20) (n := 4) (by omega)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₃.mem.writeW (stB s₀ + BitVec.ofNat 64 20) (0 : BitVec 32) := by rw [u₅.mem, u₄.gpr, u₄.mem]
  have f₅ : Frame (offR (stB s₀) [(0, 24)]) s.mem s₅.mem := by
    rw [m₅, ← k₁₂.mem]
    rw [accList_frame] at hf₃
    exact Frame.writeOff (hf₃.offR_sub (by decide) (by decide)) (a := 0) (len := 24) (by decide) (by omega)
      (by omega) (by omega) _ rfl
  have hs₅0 : s₅.gpr .r0 = s₀.gpr .r0 := by rw [u₅.gpr, u₄.other _ (by decide), hg₃, hs₂0]
  have hw₅ : stR (s₀.gpr .r0) ∈ s₅.wr := by rw [u₅.wr, u₄.wr, hwr₃]; exact hw₂
  refine WP.mono (restoreRegs_ok hfit hs₅0 hw₅ (hc.saved.frame f₅ (by decide) (by decide)))
    fun s' ⟨hr', k'⟩ => ?_
  have f' : Frame (offR (stB s₀) wkL) s₀.mem s'.mem := by
    rw [k'.mem]; exact hc.keeps.frame.trans (f₅.offR_sub (by decide) (by decide))
  -- The words stored.
  have w : ∀ x ∈ accList, ∀ d, x.2.1 = d → x.2.2 = false →
      s'.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₂.gpr x.1 := by
    intro x hx d hd hb
    have := hs₃ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    have hl : o + 4 ≤ 20 := by
      have : ∀ x ∈ accList, x.2.1 + 4 ≤ 20 := by decide
      exact this _ hx
    rw [k'.mem, m₅, readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]
    exact this
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), u₅.gpr, u₄.other _ (by decide), hg₃, k₁₂.gpr _ (by decide),
        hc.keeps.gpr _ (by decide)]
    · exact hr' i hi
  · rw [k'.sp, u₅.sp, u₄.sp, hsp₃, k₁₂.sp, hc.keeps.sp]
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hkey' := hkey
    rw [← key_frame f' (by decide) (by decide)] at hkey'
    refine ⟨?_, hkey', ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega
    · have e0 := w _ (by decide : (Reg.r3, 0, false) ∈ accList) 0 rfl rfl
      have e4 := w _ (by decide : (Reg.r5, 4, false) ∈ accList) 4 rfl rfl
      have e8 := w _ (by decide : (Reg.r7, 8, false) ∈ accList) 8 rfl rfl
      have e12 := w _ (by decide : (Reg.r10, 12, false) ∈ accList) 12 rfl rfl
      have e16 := w _ (by decide : (Reg.r1, 16, false) ∈ accList) 16 rfl rfl
      have e20 : s'.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = 0 := by rw [k'.mem, m₅, Mem.readW_writeW_self32]
      simp only at e0 e4 e8 e12 e16
      rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb, Poly1305.accumulate_append hlen]
      rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb] at hacc
      have hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by
        rw [hacc]; exact Poly1305.accumulate_lt _ _
      have hA : accumulate (Rn s₀) msg = A0 s₀ := by
        rw [A0, val_accD_eq hlt]; exact hacc.symm
      rw [hA, leNum_bytesAt_24, e0, e4,
        e8, e12, e16, e20, e3, e5, e7, e10, e1]
      have hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
        (blks s₀ (nb s₀))
      rw [show (0 : BitVec 32).toNat = 0 from rfl, val_words (fun j hj => hlL j (by omega)), hvL, hDv,
        Nat.mod_eq_of_lt hlt']

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hL, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => epilogue_ok hp hc)
  refine WP.ite s₁.z (eval_eq _) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by rw [h] at hz; simp only [nb]; rw [eq_of_beq hz.symm]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hL.toCommon)
  · have hpos : 0 < nb s₀ := by
      rw [h] at hz
      refine Nat.pos_of_ne_zero fun h' => ?_
      have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [nb] using h')
      simp [this] at hz
    refine WP.loop (M := isa) (fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s) ?_ (nb s₀) s₁
      ⟨0, rfl, hpos, hL⟩
    rintro m s ⟨i, rfl, hi, hLi⟩
    refine WP.mono (body_ok hp hi hLi) fun s' h' => ?_
    rcases h' with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩

/-! ## Constant time -/

/-- The initial taint of `blocks`: `r0`–`r2` are public, and `r0` points at
the state, whose public slots (the block pointer and count) the analysis
tracks. -/
def τb : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [128], bases := [(.r0, 0)] }

theorem wfb {s : State} (h : Proof.Poly1305.blocksArm.pre s) : VG.Arm.Taint.Wf τb s := by
  have hp := BPre.of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, τb], by simp [hp.wr], ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.mem_singleton, forall_eq]
    rw [addr_toNat]; exact hp.st_fit
  · intro p hp'; simp only [τb, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]

theorem agreeb {s₁ s₂ : State} (h₁ : Proof.Poly1305.blocksArm.pre s₁) (h₂ : Proof.Poly1305.blocksArm.pre s₂)
    (hpub : Proof.Poly1305.blocksArm.pub s₁ s₂) : VG.Arm.Taint.Agree τb s₁ s₂ := by
  obtain ⟨p0, p1, p2⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfb h₁, wfb h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τb, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [(BPre.of s₁ h₁).wr, (BPre.of s₂ h₂).wr, p0]

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_verified : Verified Arm.target Impl.Poly1305.Arm.blocks Proof.Poly1305.blocksArm := by
  refine ⟨fun s hs => blocks_correct (BPre.of s hs), ?_, ?_⟩
  · exact VG.Taint.constantTime (A := taint) τb (fun _ _ h₁ h₂ hp => agreeb h₁ h₂ hp) (by taint_decide)
  · refine ⟨blocksSat, rfl, rfl, ?_, by decide, by decide⟩
    intro a h₁ h₂
    simp only [Region.Contains, blocksSat, State.addr] at h₁ h₂
    bv_omega

end VG.Proof.Poly1305.Arm
