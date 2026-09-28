import VerifiedGarbage.Proof.Poly1305.Arm.Tail

/-!
# Poly1305 on 32-bit ARM: `finalize`

Untrusted: everything here is checked by Lean. After saving the registers
(`start_ok`) and copying and padding a non-empty tail into `out`
(`copyTail_ok`), the tail's length and `out` are stored in the state, the
limbs of `r` computed and the accumulator loaded (`setup_ok`); a non-empty
tail is absorbed (`last_ok`); then the columns are reduced fully, `s` is
added, and the sum is carried and stored modulo `2¹²⁸` in `out`
(`tag_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes mac)

/-- What `finalize` may change: `[0, 24)` and `[56, 128)` of the state, and `out`. -/
abbrev fk (s₀ : State) : List Region := offR (stB s₀) wkL ++ [oR s₀]

theorem fk_left {s₀ : State} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR (stB s₀) l) m m')
    (h : (l.all fun p => wkL.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true) : Frame (fk s₀) m m' :=
  (hf.offR_sub h (by decide)).mono fun _ hr => List.mem_append_left _ hr

theorem fk_right {s₀ : State} {m m' : Mem} (hf : Frame [oR s₀] m m') : Frame (fk s₀) m m' :=
  hf.mono fun _ hr => List.mem_append_right _ hr

/-- A word of the state is unchanged by writes to `out`. -/
theorem FPre.stWord {s₀ : State} (hp : FPre s₀) {m m' : Mem} (hf : Frame [oR s₀] m m') {d : Nat}
    (hd : d + 4 ≤ 128) : m'.readW (stB s₀ + BitVec.ofNat 64 d) 32 = m.readW (stB s₀ + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_o.sub_left (sub_base _ hd (by omega))) (by decide)

/-- A byte of `out` is unchanged by writes to the state. -/
theorem FPre.outByte {s₀ : State} (hp : FPre s₀) {l : List (Nat × Nat)} {m m' : Mem}
    (hf : Frame (offR (stB s₀) l) m m') (hl : (l.all fun p => p.1 + p.2 ≤ 128) = true) {k : Nat} (hk : k < 16) :
    m' (oB s₀ + BitVec.ofNat 64 k) = m (oB s₀ + BitVec.ofNat 64 k) := by
  refine hf _ fun r hr hc => ?_
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  have := List.all_eq_true.mp hl p hp'
  simp only [decide_eq_true_eq] at this
  exact hp.st_o _ (sub_base _ this (by omega) _ hc) (contains_off (by omega) (by omega))

theorem accD_of_words {m m' : Mem} {B : Addr}
    (h : ∀ i < 5, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (4 * i)) 32) :
    accD m' B = accD m B := by
  have hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by simp only [hwd, h i hi]
  funext k
  simp only [accD, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega)]

/-! ## Saving the registers -/

theorem start_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (saveRegs ++ [.cmp .r2 (.imm 0)])) s₀ fun s =>
      S1 s₀ s ∧ Saved (stB s₀) s₀.gpr s.mem ∧ Frame (offR (stB s₀) [(56, 32)]) s₀.mem s.mem ∧
        s.z = (s₀.gpr .r2 == 0) := by
  have hw : stR (s₀.gpr .r0) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  refine WP.append (saveRegs_ok hp.st_fit rfl hw) fun s₁ ⟨hsv, hf₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₂ u₂ hz => WP.block_nil ⟨⟨by rw [u₂.gpr, hg₁], by rw [u₂.rd, hrd₁],
    by rw [u₂.wr, hwr₁], by rw [u₂.sp, hsp₁], by
      rw [u₂.mem]; exact hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_base _ (by omega) (by omega)⟩⟩,
    by rw [u₂.mem]; exact hsv, by rw [u₂.mem]; exact hf₁, by rw [hz, hg₁]; simp⟩

/-! ## Setup -/

/-- After the setup, whether or not the tail was copied. -/
structure FS (s₀ : State) (s : State) : Prop where
  keeps : KeepsF work (fk s₀) s₀ s
  saved : Saved (stB s₀) s₀.gpr s.mem
  r : ∀ k < 10, rval s.mem (stB s₀) k = Rl s₀ k
  out : 0 < tl s₀ → OutHas s.mem (oB s₀) (padded s₀)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r3
  acc : ColsD (accD s₀.mem (stB s₀)) (stB s₀) s
  z : s.z = (s₀.gpr .r2 == 0)

theorem setup_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : S1 s₀ s₁) (hsv : Saved (stB s₀) s₀.gpr s₁.mem)
    (hf₁ : Frame (offR (stB s₀) [(56, 32)]) s₀.mem s₁.mem) {s₂ : State}
    (h₂ : KeepsF [.r1, .r4, .r5, .r12] [oR s₀] s₁ s₂) (ho₂ : 0 < tl s₀ → OutHas s₂.mem (oB s₀) (padded s₀)) :
    WP isa (.block ([.str .r3 .r0 cntOff, .str .r2 .r0 ptrOff] ++ setupR ++ loadAcc ++
      [.ldr .r1 .r0 ptrOff, .cmp .r1 (.imm 0)])) s₂ (FS s₀) := by
  have hfit := hp.st_fit
  have g : ∀ r, r ∉ [Reg.r1, .r4, .r5, .r12] → s₂.gpr r = s₀.gpr r := fun r hr => by rw [h₂.gpr r hr, h₁.gpr]
  have hw₂ : stR (s₀.gpr .r0) ∈ s₂.wr := by rw [h₂.wr, h₁.wr, hp.wr]; exact List.mem_cons_self
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [g .r0 (by decide)]; exact ea hfit (off := 20) (by omega)) (outSt hw₂ (off := 20) (n := 4) (by omega))
    fun s₃ u₃ => ?_
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [u₃.gpr, g .r0 (by decide)]; exact ea hfit (off := 124) (by omega))
    (by rw [u₃.wr]; exact outSt hw₂ (off := 124) (n := 4) (by omega)) fun s₄ u₄ => ?_
  have m₄ : s₄.mem = (s₂.mem.writeW (stB s₀ + BitVec.ofNat 64 20) (s₀.gpr .r3)).writeW
      (stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r2) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, g .r3 (by decide), g .r2 (by decide)]
  have f₂₄ : Frame (offR (stB s₀) [(20, 4), (124, 4)]) s₂.mem s₄.mem := by
    rw [m₄]
    exact Frame.writeOff (Frame.writeOff (Frame.refl _ _) (a := 20) (len := 4) (by decide) le_rfl le_rfl
      (by omega) _ rfl) (a := 124) (len := 4) (by decide) le_rfl le_rfl (by omega) _ rfl
  have hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [u₄.gpr, u₃.gpr, g .r0 (by decide)]
  have hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [u₄.wr, u₃.wr]; exact hw₂
  rw [← List.append_assoc setupR loadAcc]
  refine WP.append (setupAcc_ok hfit hs₄0 hw₄) fun s₅ ⟨hr₅, hc₅, k₅⟩ => ?_
  have hs₅0 : s₅.gpr .r0 = s₀.gpr .r0 := by rw [k₅.gpr _ (by decide), hs₄0]
  have hw₅ : stR (s₀.gpr .r0) ∈ s₅.wr := by rw [k₅.wr]; exact hw₄
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [hs₅0]; exact ea hfit (off := 124) (by omega)) (inSt hw₅ (off := 124) (n := 4) (by omega))
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ u₇ hz => WP.block_nil ?_
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  have f₂₅ : Frame (offR (stB s₀) [(0, 20), (20, 4), (88, 36), (124, 4)]) s₂.mem s₅.mem :=
    (f₂₄.offR_sub (by decide) (by decide)).trans (k₅.frame.offR_sub (by decide) (by decide))
  -- The state's words on entry to `setupAcc`: those of `s₀` but for the saved registers and the stores.
  have hw₁₂ : ∀ d, d + 4 ≤ 128 → s₂.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 =
      s₁.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 := fun d hd => hp.stWord h₂.frame hd
  have hRl : rlimb s₄.mem (stB s₀) = Rl s₀ := by
    rw [rlimb_frame' f₂₄ (by decide) (by decide), rlimb_frame fun i hi => hw₁₂ _ (by omega),
      rlimb_frame' hf₁ (by decide) (by decide)]
  have hA : accD s₄.mem (stB s₀) = accD s₀.mem (stB s₀) := by
    rw [accD_frame f₂₄ (by decide) (by decide), accD_of_words fun i hi => hw₁₂ _ (by omega),
      accD_frame hf₁ (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun k hk => ?_, fun hpos k hk => ?_, ?_, ⟨fun k hk => ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    rw [u₇.gpr, u₆.other _ h1, k₅.gpr _ (by
      simp only [yregs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)),
      u₄.gpr, u₃.gpr, g r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨h1, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide))]
  · rw [m₇]
    exact (fk_left hf₁ (by decide)).trans ((fk_right h₂.frame).trans (fk_left f₂₅ (by decide)))
  · rw [u₇.rd, u₆.rd, k₅.rd, u₄.rd, u₃.rd, h₂.rd, h₁.rd]
  · rw [u₇.wr, u₆.wr, k₅.wr, u₄.wr, u₃.wr, h₂.wr, h₁.wr]
  · rw [u₇.sp, u₆.sp, k₅.sp, u₄.sp, u₃.sp, h₂.sp, h₁.sp]
  · rw [m₇]
    intro i hi
    rw [f₂₅.readW (Region.contains_self _ _) (fun r hr => (dj_offR _ (d := 56) (n := 32) (by decide) (by omega)
      (by decide) r hr).sub_left (sub_sub _ (by omega) (by omega) (by omega))) (by decide), hp.stWord h₂.frame (by omega)]
    exact hsv i hi
  · rw [m₇, ← hRl]; exact hr₅ k hk
  · rw [m₇, hp.outByte f₂₅ (by decide) hk]; exact ho₂ hpos k hk
  · rw [m₇, k₅.frame.word (by decide) (by decide) (by decide), m₄,
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · have := yr_ne k hk
    rw [u₇.gpr, u₆.other _ this.2.1, ← hA]; exact hc₅.1 k hk
  · rw [m₇, ← hA]; exact hc₅.2
  · rw [hz, u₆.gpr, k₅.frame.word (by decide) (by decide) (by decide), m₄, Mem.readW_writeW_self32]; simp

/-! ## The last block -/

/-- Before the final reduction. -/
structure FL (s₀ : State) (s : State) : Prop where
  keeps : KeepsF work (fk s₀) s₀ s
  saved : Saved (stB s₀) s₀.gpr s.mem
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r3
  acc : ∃ D, ColsD D (stB s₀) s ∧ (∀ k < 10, D k ≤ 3564723200) ∧
    val D % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P

theorem tail_nil {s₀ : State} (h : tl s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem last_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : FS s₀ s) (hpos : 0 < tl s₀) :
    WP isa (.block (.ldr .r1 .r0 cntOff :: absorb false)) s (FL s₀) := by
  have hfit := hp.st_fit
  have htl := hp.tl_lt
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  have hw : stR (s₀.gpr .r0) ∈ s.wr := by rw [h.keeps.wr, hp.wr]; exact List.mem_cons_self
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide) (by rw [hs0]; exact ea hfit (off := 20) (by omega))
    (inSt hw (off := 20) (n := 4) (by omega)) fun s₁ u₁ => ?_
  rw [← List.append_nil (absorb false)]
  have hr1 : s₁.gpr .r1 = s₀.gpr .r3 := by rw [u₁.gpr, h.cnt]
  have hoW : oR s₀ ∈ s₁.wr := by
    rw [u₁.wr, h.keeps.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hin : ∀ j < 4, InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 :=
    fun j hj => by
      rw [hr1, eaO hp (by omega)]
      exact ⟨_, List.mem_append_right _ hoW, contains_off (by omega) (by omega)⟩
  have hmsg : msgVal s₁ = leNum (tail s₀ ++ [0x01]) := by
    rw [← padded_value hp (m := s₁.mem) (fun k hk => by rw [u₁.mem]; exact h.out hpos k hk), leNum_bytesAt_16]
    simp only [msgVal, word, hr1]
    rw [eaO hp (d := 4 * 0) (by omega), eaO hp (d := 4 * 1) (by omega), eaO hp (d := 4 * 2) (by omega),
      eaO hp (d := 4 * 3) (by omega)]
  refine WP.append (absorb_ok hfit false (R := Rl s₀) (D := accD s₀.mem (stB s₀)) (fun i _ => rlimb_lt _ _ i)
      (fun k _ => by
      have := accD_lt s₀.mem (stB s₀) k; omega)
      (by rw [u₁.other _ (by decide), hs0]) (by rw [u₁.wr]; exact hw)
      (fun k hk => by rw [u₁.mem]; exact h.r k hk)
      ⟨fun k hk => by rw [u₁.other _ (yr_ne k hk).2.1]; exact h.acc.1 k hk, by rw [u₁.mem]; exact h.acc.2⟩ hin)
    fun s₂ ⟨D, hc₂, hb₂, hv₂, k₂⟩ => WP.block_nil ⟨?_, ?_, ?_, D, hc₂, hb₂, ?_⟩
  · have f₂ : Frame (offR (stB s₀) [(0, 20)]) s₁.mem s₂.mem := by rw [← accR_offR]; exact k₂.frame
    refine h.keeps.trans ⟨fun r hr => ?_, ?_, by rw [k₂.rd, u₁.rd], by rw [k₂.wr, u₁.wr], by rw [k₂.sp, u₁.sp]⟩
    · rw [k₂.gpr _ hr, u₁.other _ (by rintro rfl; exact hr (by decide))]
    · rw [u₁.mem] at f₂
      exact fk_left f₂ (by decide)
  · have f₂ : Frame (offR (stB s₀) [(0, 20)]) s.mem s₂.mem := by
      rw [← accR_offR, ← u₁.mem]; exact k₂.frame
    exact h.saved.frame f₂ (by decide) (by decide)
  · have f₂ : Frame (offR (stB s₀) [(0, 20)]) s.mem s₂.mem := by
      rw [← accR_offR, ← u₁.mem]; exact k₂.frame
    rw [f₂.word (by decide) (by decide) (by decide)]; exact h.cnt
  · have hl : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv₂, hmsg, Poly1305.absorbAll_block (by omega) (by omega), Nat.mod_mod]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    rw [Nat.mul_comm]

/-! ## The tag -/

/-- The tag's stores. -/
def tagList : List (Reg × Nat × Bool) := [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false)]

theorem tag_eq : [Instr.ldr .r2 .r0 cntOff, .str .r3 .r2 0, .str .r5 .r2 4, .str .r7 .r2 8, .str .r10 .r2 12] ++
    restoreRegs = .ldr .r2 .r0 cntOff :: (tagList.map (storeI .r2) ++ restoreRegs) := rfl

/-- The sum of `h mod p` and `s`, carried. -/
def sumL (D : Nat → Nat) (w : Nat → Nat) : Nat → Nat := fun k => redL D k + mlimb (w 0) (w 1) (w 2) (w 3) k

theorem tag_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : FL s₀ s) :
    WP isa (.block (reduce ++ [.str .r1 .r0 d9Off, .dp .add .r1 .r0 (.imm 40)] ++ addWords ++ addTop false ++
      mask :: (List.range 9).flatMap carryStep ++ toWords ++
      [.ldr .r2 .r0 cntOff, .str .r3 .r2 0, .str .r5 .r2 4, .str .r7 .r2 8, .str .r10 .r2 12] ++
      restoreRegs)) s fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  have hfit := hp.st_fit
  obtain ⟨D, hcD, hDb, hDv⟩ := h.acc
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  have hw : stR (s₀.gpr .r0) ∈ s.wr := by rw [h.keeps.wr, hp.wr]; exact List.mem_cons_self
  have hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega
  obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (reduce_ok hfit hDb hs0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  have hs₁0 : s₁.gpr .r0 = s₀.gpr .r0 := by rw [k₁.gpr _ (by decide), hs0]
  have hw₁ : stR (s₀.gpr .r0) ∈ s₁.wr := by rw [k₁.wr]; exact hw
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 16) (by decide) (by rw [hs₁0]; exact ea hfit (off := 16) (by omega))
    (outSt hw₁ (off := 16) (n := 4) (by omega)) fun s₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  have hr1 : s₃.gpr .r1 = s₀.gpr .r0 + 40 := by rw [u₃.gpr, u₂.gpr, hs₁0]
  have hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  have hsA : ∀ i < 4, State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * i)) = stB s₀ + BitVec.ofNat 64 (40 + 4 * i) :=
    fun i hi => by
      rw [hr1, BitVec.add_assoc, show (40 : BitVec 32) = BitVec.ofNat 32 40 from rfl, ← BitVec.ofNat_add]
      exact ea hfit (by omega)
  refine WP.append (addWords_ok fun i hi => by rw [hsA i hi]; exact inSt hw₃ (by omega)) fun s₄ ⟨hc₄, hr₄, k₄⟩ => ?_
  -- The words of `s`.
  let w : Nat → Nat := fun i => (s₀.mem.readW (stB s₀ + BitVec.ofNat 64 (40 + 4 * i)) 32).toNat
  have m₃ : s₃.mem = s₁.mem.writeW (stB s₀ + BitVec.ofNat 64 16) (s₁.gpr .r1) := by rw [u₃.mem, u₂.mem]
  have hf₀₃ : Frame (fk s₀) s₀.mem s₃.mem := by
    rw [m₃, k₁.mem]
    exact Frame.writeW h.keeps.frame (List.mem_append_left _ (List.mem_map.mpr ⟨(0, 24), by decide, rfl⟩)) _
      (contains_sub _ (by omega) (by omega) (by omega))
  have hword : ∀ i < 4, (word s₃ i).toNat = w i := fun i hi => by
    simp only [word, w]
    rw [hsA i hi, hf₀₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    rcases List.mem_append.mp hr with hr | hr
    · exact (dj_offR _ (d := 24) (n := 32) (by decide) (by omega) (by decide) r hr).sub_left
        (sub_sub _ (by omega) (by omega) (by omega))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (sub_base _ (by omega) (by omega))
  have hw4 : ∀ i, w i < 2 ^ 32 := fun i => BitVec.isLt _
  have hml := fun k => mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
  -- `addTop false`: the top column.
  simp only [addTop, Bool.false_eq_true, ite_false, List.append_nil, List.cons_append, List.nil_append]
  have hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), u₃.other _ (by decide), u₂.gpr, hs₁0]
  have hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 16) (by decide) (by rw [hs₄0]; exact ea hfit (off := 16) (by omega))
    (inSt hw₄ (off := 16) (n := 4) (by omega)) fun s₅ u₅ => wp_add (op2_lsr (by omega)) fun s₆ u₆ => ?_
  refine wp_movw fun s₇ u₇ => ?_
  have hL9 := hlL 9 (by omega)
  have hcols : Cols (sumL D w) s₇ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with hj9 | hj9
    · have hne := yr_ne j hj9
      have e₁ := hc₁ j hj
      have := hlL j hj; have := hml j
      rw [u₇.other _ hne.2.2.1, u₆.other _ hne.2.1, u₅.other _ hne.2.1, hc₄ j hj9,
        u₃.other _ hne.2.1, u₂.gpr, toNat_add_lt (by rw [e₁, wsum_toNat _ hj9, hword 0 (by omega),
          hword 1 (by omega), hword 2 (by omega), hword 3 (by omega)]; omega), e₁, wsum_toNat _ hj9,
        hword 0 (by omega), hword 1 (by omega), hword 2 (by omega), hword 3 (by omega)]
      rfl
    · have e9 : (s₅.gpr .r1).toNat = redL D 9 := by
        rw [u₅.gpr, k₄.mem, m₃, Mem.readW_writeW_self32]; exact hc₁ 9 (by omega)
      have e2 : (s₅.gpr .r2).toNat = w 3 := by
        rw [u₅.other _ (by decide), hr₄, hword 3 (by omega)]
      have := hml 9
      rw [show j = 9 by omega, yr9, u₇.other _ (by decide), u₆.gpr, toNat_add_lt (by rw [e9, toNat_shr, e2]; omega),
        e9, toNat_shr, e2]
      rfl
  have hfb : ∀ j < 10, sumL D w j < 2 ^ 32 - 2 ^ 19 := fun j hj => by
    have := hlL j hj; have := hml j; simp only [sumL]; omega
  refine WP.append (carries_ok 0 9 (by omega) hfb hcols u₇.gpr) fun s₈ ⟨hc₈, k₈⟩ => ?_
  have hL : ∀ j < 9, carryN (sumL D w) 0 9 j < 2 ^ 13 := fun j hj => carryN_lt _ 0 9 j (by omega) (by omega)
  refine WP.append (toWords_ok hc₈ hL) fun s₉ ⟨e3, e5, e7, e10, _, k₉⟩ => ?_
  -- The stores into `out`.
  rw [show (Instr.ldr .r2 .r0 cntOff :: .str .r3 .r2 0 :: .str .r5 .r2 4 :: .str .r7 .r2 8 :: .str .r10 .r2 12 ::
    restoreRegs) = .ldr .r2 .r0 cntOff :: (tagList.map (storeI .r2) ++ restoreRegs) from rfl]
  have m₉ : s₉.mem = s₃.mem := by
    rw [k₉.mem, k₈.mem, u₇.mem, u₆.mem, u₅.mem, k₄.mem]
  have g₉ : ∀ r, r ∉ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] → s₉.gpr r = s₀.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [k₉.gpr _ (by simp [h1, h3, h5, h7, h10]), k₈.gpr _ (by simp [cregs, yregs, h1, h3, h4, h5, h6, h7, h8, h9,
      h10, h11]), u₇.other _ h2, u₆.other _ h1, u₅.other _ h1, k₄.gpr _ (by simp [yregs, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11]), u₃.other _ h1, u₂.gpr, k₁.gpr _ (by simp [cregs, yregs, h1, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11]), h.keeps.gpr _ (by simp [work, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12])]
  have hs₉0 : s₉.gpr .r0 = s₀.gpr .r0 := g₉ _ (by decide)
  have hw₉ : stR (s₀.gpr .r0) ∈ s₉.wr := by rw [k₉.wr, k₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr]; exact hw₃
  have hrd₉ : s₉.rd = s₀.rd := by
    rw [k₉.rd, k₈.rd, u₇.rd, u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, k₁.rd, h.keeps.rd]
  have hwr₉ : s₉.wr = s₀.wr := by
    rw [k₉.wr, k₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, k₁.wr, h.keeps.wr]
  have hsp₉ : s₉.sp = s₀.sp := by
    rw [k₉.sp, k₈.sp, u₇.sp, u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, k₁.sp, h.keeps.sp]
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide) (by rw [hs₉0]; exact ea hfit (off := 20) (by omega))
    (inSt hw₉ (off := 20) (n := 4) (by omega)) fun t₁ v₁ => ?_
  have ht₁ : t₁.gpr .r2 = s₀.gpr .r3 := by
    rw [v₁.gpr, m₉, m₃, readW_writeW_off _ _ _ (by omega) (by omega) (by omega), k₁.mem]; exact h.cnt
  have hoW : (⟨oB s₀, 16⟩ : Region) ∈ t₁.wr := by
    rw [v₁.wr, hwr₉, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  refine WP.append (stores_ok .r2 hp.o_fit rfl tagList t₁ ht₁ hoW (by decide) (by decide))
    fun t₂ ⟨hs₂, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  have hfo : Frame [oR s₀] t₁.mem t₂.mem := hf₂.sub fun r hr => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hb : ∀ x ∈ tagList, x.2.1 + ssize x.2.2 ≤ 16 := by decide
    exact ⟨_, List.mem_singleton_self _, sub_base _ (hb x hx) (by omega)⟩
  have hs₂0 : t₂.gpr .r0 = s₀.gpr .r0 := by rw [hg₂, v₁.other _ (by decide), hs₉0]
  have hw₂ : stR (s₀.gpr .r0) ∈ t₂.wr := by rw [hwr₂, v₁.wr]; exact hw₉
  have hsv : Saved (stB s₀) s₀.gpr t₂.mem := by
    intro i hi
    rw [hp.stWord hfo (by omega), v₁.mem, m₉, m₃, k₁.mem]
    have := h.saved.frame (l := [(16, 4)]) (m' := s.mem.writeW (stB s₀ + BitVec.ofNat 64 16) (s₁.gpr .r1))
      (Frame.writeOff (Frame.refl _ _) (a := 16) (len := 4) (by decide) le_rfl le_rfl (by omega) _ rfl)
      (by decide) (by decide)
    exact this i hi
  refine WP.mono (restoreRegs_ok hfit hs₂0 hw₂ hsv) fun s' ⟨hr', k'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), hg₂, v₁.other _ (by decide), g₉ _ (by decide)]
    · exact hr' i hi
  · rw [k'.sp, hsp₂, v₁.sp, hsp₉]
  · intro key msg hrep
    obtain ⟨hlen, hkey, hacc⟩ := hrep
    -- The tag's words.
    have wd : ∀ x ∈ tagList, ∀ d, x.2.1 = d → x.2.2 = false →
        (s'.mem.readW (oB s₀ + BitVec.ofNat 64 d) 32).toNat = (s₉.gpr x.1).toNat := by
      intro x hx d hd hb
      have := hs₂ x hx
      obtain ⟨r, o, b⟩ := x
      simp only at hd hb; subst hd hb
      have hr2 : r ≠ .r2 := by
        have : ∀ x ∈ tagList, x.1 ≠ .r2 := by decide
        exact this _ hx
      rw [k'.mem]; simp only [Stored] at this; rw [this, v₁.other _ hr2]
    have e0 := wd _ (by decide : (Reg.r3, 0, false) ∈ tagList) 0 rfl rfl
    have e4 := wd _ (by decide : (Reg.r5, 4, false) ∈ tagList) 4 rfl rfl
    have e8 := wd _ (by decide : (Reg.r7, 8, false) ∈ tagList) 8 rfl rfl
    have e12 := wd _ (by decide : (Reg.r10, 12, false) ∈ tagList) 12 rfl rfl
    simp only at e0 e4 e8 e12
    rw [e3] at e0; rw [e5] at e4; rw [e7] at e8; rw [e10] at e12
    have b0 := (s₉.gpr .r3).isLt; have b1 := (s₉.gpr .r5).isLt; have b2 := (s₉.gpr .r7).isLt
    have b3 := (s₉.gpr .r10).isLt
    rw [e3] at b0; rw [e5] at b1; rw [e7] at b2; rw [e10] at b3
    have hv : val (carryN (sumL D w) 0 9) = tw0 (carryN (sumL D w) 0 9) + 2 ^ 32 * tw1 (carryN (sumL D w) 0 9) +
        2 ^ 64 * tw2 (carryN (sumL D w) 0 9) + 2 ^ 96 * tw3 (carryN (sumL D w) 0 9) +
        2 ^ 128 * (carryN (sumL D w) 0 9 9 / 2 ^ 11) := by
      rw [val_toWords hL]; rfl
    have hvs : val (carryN (sumL D w) 0 9) = val (redL D) + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3) := by
      rw [val_carryN _ 0 9 (by omega), ← val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)]
      simp only [val, sumL]; ring
    -- The key.
    rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb] at hacc
    have hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by rw [hacc]; exact Poly1305.accumulate_lt _ _
    have hA : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, val_accD_eq hlt]; exact hacc.symm
    have hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
      (tail s₀)
    have hS : leNum (((bytesAt s₀.mem (stB s₀ + 24) 32).drop 16).take 16) =
        w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3 := by
      rw [(drop_bytesAt s₀.mem (stB s₀ + 24) 16 16 : (bytesAt s₀.mem (stB s₀ + 24) 32).drop 16 = _),
        take_bytesAt _ _ le_rfl, leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add, off_add,
        off_add, off_add, off_add]
    simp only [Spec.Poly1305.mac]
    rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb, Poly1305.accumulate_append hlen, hA, hS,
      k'.mem, Poly1305.bytesAt_leBytes, ← Poly1305.leNum_bytesAt_read, leNum_bytesAt_16]
    rw [k'.mem] at e0 e4 e8 e12
    rw [e0, e4, e8, e12]
    have key : tw0 (carryN (sumL D w) 0 9) + 2 ^ 32 * tw1 (carryN (sumL D w) 0 9) +
        2 ^ 64 * tw2 (carryN (sumL D w) 0 9) + 2 ^ 96 * tw3 (carryN (sumL D w) 0 9) =
        (Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3)) %
          256 ^ 16 := by
      rw [hvL, hDv, Nat.mod_eq_of_lt hlt'] at hvs
      rw [show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num]
      omega
    rw [key, Poly1305.leBytes_mod]

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  refine WP.seq (WP.mono (start_ok hp) fun s₁ ⟨h₁, hsv, hf₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => KeepsF [.r1, .r4, .r5, .r12] [oR s₀] s₁ s ∧
    (0 < tl s₀ → OutHas s.mem (oB s₀) (padded s₀))) ?_ fun s₂ ⟨h₂, ho₂⟩ => ?_)
  · refine WP.ite s₁.z (eval_eq _) (fun h => ?_) (fun h => ?_)
    · have h0 : tl s₀ = 0 := by
        rw [h] at hz₁; simp only [tl]; rw [eq_of_beq hz₁.symm]; rfl
      exact WP.block_nil (M := isa) ⟨(Keeps.refl _ _).keepsF _, fun hpos => absurd hpos (by omega)⟩
    · have hpos : 0 < tl s₀ := by
        rw [h] at hz₁
        refine Nat.pos_of_ne_zero fun h' => ?_
        have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [tl] using h')
        simp [this] at hz₁
      exact WP.mono (copyTail_ok hp h₁ hpos) fun s h => ⟨h.1, fun _ => h.2⟩
  refine WP.seq (WP.mono (setup_ok hp h₁ hsv hf₁ h₂ ho₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (Q := FL s₀) ?_ fun s₄ h₄ => tag_ok hp h₄)
  refine WP.ite s₃.z (eval_eq _) (fun h => ?_) (fun h => ?_)
  · have hz := h₃.z
    have h0 : tl s₀ = 0 := by
      rw [h] at hz; simp only [tl]; rw [eq_of_beq hz.symm]; rfl
    refine WP.block_nil (M := isa) ⟨h₃.keeps, h₃.saved, h₃.cnt, accD s₀.mem (stB s₀), h₃.acc,
      fun k _ => by have := accD_lt s₀.mem (stB s₀) k; omega, ?_⟩
    rw [tail_nil h0, Poly1305.absorbAll_nil]
  · have hz := h₃.z
    have hpos : 0 < tl s₀ := by
      rw [h] at hz
      refine Nat.pos_of_ne_zero fun h' => ?_
      have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [tl] using h')
      simp [this] at hz
    exact last_ok hp h₃ hpos

/-! ## Constant time -/

/-- The initial taint of `finalize`: `r0`–`r3` are public, and `r0` and `r3`
point at the state and `out`; the analysis tracks the public slots of the
state (the tail's length and `out`). -/
def τf : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 16], bases := [(.r0, 0), (.r3, 1)] }

theorem wff {s : State} (h : Proof.Poly1305.finalizeArm.pre s) : VG.Arm.Taint.Wf τf s := by
  have hp := FPre.of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, τf], by simpa [hp.wr] using hp.st_o, ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat]
    · exact hp.st_fit
    · exact hp.o_fit
  · intro p hp'
    simp only [τf, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agreef {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeArm.pre s₁) (h₂ : Proof.Poly1305.finalizeArm.pre s₂)
    (hpub : Proof.Poly1305.finalizeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τf s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wff h₁, wff h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τf, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [(FPre.of s₁ h₁).wr, (FPre.of s₂ h₂).wr, p0, oR, oB, oR, oB, p3]

/-- A state satisfying the precondition (with no tail). -/
def finalizeSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩]

theorem finalize_verified : Verified Arm.target Impl.Poly1305.Arm.finalize Proof.Poly1305.finalizeArm := by
  refine ⟨fun s hs => finalize_correct (FPre.of s hs), ?_, ?_⟩
  · exact VG.Taint.constantTime (A := taint) τf (fun _ _ h₁ h₂ hp => agreef h₁ h₂ hp) (by taint_decide)
  · refine ⟨finalizeSat, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, finalizeSat, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.Arm
