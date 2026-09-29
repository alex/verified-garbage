import VerifiedGarbage.Proof.Poly1305.Arm.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305 on 32-bit ARM: the steps of `update` and `finalize`

Untrusted: everything here is checked by Lean. At a block boundary (`Acc`),
the columns are congruent modulo `p` to an accumulator followed by some
blocks; absorbing a block (`absorbAcc_ok`), the loop body of `blocks` over
any blocks (`body_gen`), and reducing and storing the accumulator
(`storeAcc_ok`) keep track of them. The callee-saved registers are saved in
and restored from `scratch` (`saveScr_ok`, `restoreScr_ok`), and bytes are
copied into the buffer, bytes 56–71 of the state (`copy_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P leNum bytesAt)

/-! ## At a block boundary -/

/-- `r0` points at the state `st`, which stores the limbs `R` of `r`, and the
columns (`ColsD`) are congruent modulo `p` to the accumulator `A` followed by
the blocks `X`. -/
structure Acc (st : BitVec 32) (R : Nat → Nat) (A : Nat) (X : List Byte) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  wr : stR st ∈ s.wr
  r : ∀ k < 10, rval s.mem (State.addr st) k = R k
  acc : ∃ D, ColsD D (State.addr st) s ∧ (∀ k < 10, D k ≤ 3564723200) ∧
    val D % P = Poly1305.absorbAll (val R) A X % P

/-- `Acc` holds while the registers `r0` and `r3`–`r11`, the writable regions
and the state's words at `[16, 20)` and `[88, 124)` stay. -/
theorem Acc.keep {st : BitVec 32} {R : Nat → Nat} {A : Nat} {X : List Byte} {s s' : State}
    (h : Acc st R A X s) {ws : List Reg} {l : List (Nat × Nat)} (hk : KeepsF ws (offR (State.addr st) l) s s')
    (hws : (ws.all fun r => r != .r0 && !yregs.contains r) = true)
    (hl : (l.all fun p => (20 ≤ p.1 ∨ p.1 + p.2 ≤ 16) ∧ (124 ≤ p.1 ∨ p.1 + p.2 ≤ 88)) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : Acc st R A X s' := by
  have hn : ∀ r ∈ ws, r ≠ .r0 ∧ r ∉ yregs := fun r hr => by
    have := List.all_eq_true.mp hws r hr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at this
    exact this
  obtain ⟨D, hcD, hDb, hDv⟩ := h.acc
  refine ⟨by rw [hk.gpr _ fun h' => (hn _ h').1 rfl, h.r0], by rw [hk.wr]; exact h.wr,
    fun k hk' => ?_, D, ⟨fun k hk' => ?_, ?_⟩, hDb, hDv⟩
  · rw [rval_frame' hk.frame (by
      rw [List.all_eq_true] at hl ⊢
      intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; exact this.2) hl' hk']
    exact h.r k hk'
  · rw [hk.gpr _ fun h' => (hn _ h').2 (yr_yregs k hk')]; exact hcD.1 k hk'
  · rw [hk.frame.word (by
      rw [List.all_eq_true] at hl ⊢
      intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega) (by omega) hl']
    exact hcD.2

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- Absorbing the block at `a`, at `r1`. -/
theorem absorbAcc_ok {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc st R A X s) {a : Addr}
    (ha : ∀ j < 4, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) = a + BitVec.ofNat 64 (4 * j))
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (absorb true)) s fun s' =>
      Acc st R A (X ++ bytesAt s.mem a 16) s' ∧ KeepsF work [accR (State.addr st)] s s' := by
  obtain ⟨D, hcD, hDb, hDv⟩ := h.acc
  refine WP.mono (absorb_ok hfit true hR hDb h.r0 h.wr h.r hcD fun j hj => by rw [ha j hj]; exact hin j hj)
    fun s' ⟨D', hc', hb', hv', k'⟩ => ⟨⟨?_, ?_, fun k hk => ?_, D', hc', hb', ?_⟩, k'⟩
  · rw [k'.gpr _ (by decide), h.r0]
  · rw [k'.wr]; exact h.wr
  · rw [rval_frame k'.frame hk]; exact h.r k hk
  · have hmsg : msgVal s = leNum (bytesAt s.mem a 16) := by
      rw [leNum_bytesAt_16, msgVal]
      simp only [word]
      rw [ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
    have hl := Poly1305.length_bytesAt s.mem a 16
    rw [Poly1305.absorbAll_append hX, Poly1305.absorbAll_block (by omega) (by omega), hv', hmsg,
      leNum_pad _ hl, iteT rfl, Nat.add_assoc]
    exact mod_step hDv

/-- The loop body of `blocks`, with the block pointer `p` and the count `c`
stored in the state. -/
theorem body_gen {R : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13) {A : Nat} {X : List Byte}
    (hX : X.length % 16 = 0) {s : State} (h : Acc st R A X s) {p : BitVec 32} {c : Nat}
    (hptr : s.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p)
    (hcnt : s.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 c) (hc : 0 < c)
    (hc32 : c < 2 ^ 32) (hpf : p.toNat + 16 ≤ 2 ^ 32)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 (4 * j)) 4)
    (hd : (⟨State.addr p, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 124, 4⟩) :
    WP isa body s fun s' => Acc st R A (X ++ bytesAt s.mem (State.addr p) 16) s' ∧
      KeepsF work (offR (State.addr st) [(0, 24), (124, 4)]) s s' ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 124) 32 = p + 16 ∧
      s'.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (c - 1) ∧
      s'.z = decide (c - 1 = 0) := by
  have hs0 := h.r0
  have hw := h.wr
  rw [body_eq, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [hs0]; exact ea hfit (off := 124) (by omega)) (inSt hw (off := 124) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 124) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact ea hfit (off := 124) (by omega))
    (by rw [u₂.wr, u₁.wr]; exact outSt hw (off := 124) (n := 4) (by omega)) fun s₃ u₃ => ?_
  have hp₃ : s₃.gpr .r1 = p := by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hptr]
  have m₃ : s₃.mem = s.mem.writeW (State.addr st + BitVec.ofNat 64 124) (p + 16) := by
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hptr]
  have f₃ : Frame (offR (State.addr st) [(124, 4)]) s.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
      (by omega) _ rfl
  have k₃ : KeepsF [.r1, .r2] (offR (State.addr st) [(124, 4)]) s s₃ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1],
      f₃, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  have hA₃ : Acc st R A X s₃ := h.keep k₃ (by decide) (by decide) (by decide)
  have hblk : bytesAt s₃.mem (State.addr p) 16 = bytesAt s.mem (State.addr p) 16 :=
    bytesAt_frame f₃ (fun r hr => by
      simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr; exact hd)
      (by decide)
  rw [← List.append_nil [Instr.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff]]
  refine WP.append (absorbAcc_ok hfit hR hX hA₃ (a := State.addr p)
    (fun j hj => by rw [hp₃]; exact addr_add (by omega))
    (fun j hj => by rw [k₃.rd, k₃.wr]; exact hin j hj)) fun s₄ ⟨hA₄, k₄⟩ => ?_
  rw [hblk] at hA₄
  have hs40 : s₄.gpr .r0 = st := hA₄.r0
  have hw₄ : stR st ∈ s₄.wr := hA₄.wr
  have f₄ : Frame (offR (State.addr st) [(0, 20)]) s₃.mem s₄.mem := by rw [← accR_offR]; exact k₄.frame
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [hs40]; exact ea hfit (off := 20) (by omega)) (inSt hw₄ (off := 20) (n := 4) (by omega))
    fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₆ u₆ hz₆ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), hs40]; exact ea hfit (off := 20) (by omega))
    (by rw [u₆.wr, u₅.wr]; exact outSt hw₄ (off := 20) (n := 4) (by omega)) fun s₇ u₇ => WP.block_nil ?_
  have hc₅ : s₅.gpr .r1 = BitVec.ofNat 32 c := by
    rw [u₅.gpr, f₄.word (by decide) (by decide) (by decide), f₃.word (by decide) (by decide) (by decide), hcnt]
  have hc₆ : s₆.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u₆.gpr, hc₅, show c = (c - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
    exact BitVec.add_sub_cancel _ _
  have m₇ : s₇.mem = s₄.mem.writeW (State.addr st + BitVec.ofNat 64 20) (BitVec.ofNat 32 (c - 1)) := by
    rw [u₇.mem, hc₆, u₆.mem, u₅.mem]
  have k₄₇ : KeepsF [.r1] (offR (State.addr st) [(20, 4)]) s₄ s₇ := by
    refine ⟨fun r hr => ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd], by rw [u₇.wr, u₆.wr, u₅.wr],
      by rw [u₇.sp, u₆.sp, u₅.sp]⟩
    · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
      rw [u₇.gpr, u₆.other _ h1, u₅.other _ h1]
    · rw [m₇]
      exact Frame.writeOff (Frame.refl _ _) (a := 20) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
        (by omega) _ rfl
  refine ⟨hA₄.keep k₄₇ (by decide) (by decide) (by decide), ?_, ?_, by rw [m₇, Mem.readW_writeW_self32], ?_⟩
  · refine ((k₃.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide))).trans
      (((k₄.sub (by rw [accR_offR]; exact sub_offR _ (by decide) (by decide))).trans
        ((k₄₇.mono (by simp [work])).sub (sub_offR _ (by decide) (by decide)))))
  · rw [m₇, readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      f₄.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  · rw [u₇.z, hz₆, ← u₆.gpr, hc₆, ofNat_beq_zero (by omega)]

/-- Reducing the columns fully and storing them as the accumulator. -/
theorem storeAcc_ok {R : Nat → Nat} {A : Nat} {X : List Byte} {s : State} (h : Acc st R A X s) :
    WP isa (.block (reduce ++ toWords ++ storeAcc)) s fun s' =>
      leNum (bytesAt s'.mem (State.addr st) 24) = Poly1305.absorbAll (val R) A X % P ∧
      KeepsF work (offR (State.addr st) [(0, 24)]) s s' := by
  obtain ⟨D, hcD, hDb, hDv⟩ := h.acc
  have hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega
  obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
  simp only [List.append_assoc]
  refine WP.append (reduce_ok hfit hDb h.r0 h.wr hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  refine WP.append (toWords_ok hc₁ fun j hj => hlL j (by omega)) fun s₂ ⟨e3, e5, e7, e10, e1, k₂⟩ => ?_
  have k₁₂ := k₁.trans (k₂.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cregs, yregs])
  have hs₂0 : s₂.gpr .r0 = st := by rw [k₁₂.gpr _ (by decide), h.r0]
  have hw₂ : stR st ∈ s₂.wr := by rw [k₁₂.wr]; exact h.wr
  rw [show storeAcc = accList.map (storeI .r0) ++ [.mov .r2 (.imm 0), .str .r2 .r0 20] from rfl]
  refine WP.append (stores_ok .r0 hfit rfl accList s₂ hs₂0 hw₂ (by decide) (by decide))
    fun s₃ ⟨hs₃, hf₃, hg₃, hrd₃, hwr₃, hsp₃⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 20) (by decide)
    (by rw [u₄.other _ (by decide), hg₃, hs₂0]; exact ea hfit (off := 20) (by omega))
    (by rw [u₄.wr, hwr₃]; exact outSt hw₂ (off := 20) (n := 4) (by omega)) fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s₃.mem.writeW (State.addr st + BitVec.ofNat 64 20) (0 : BitVec 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem]
  have f₅ : Frame (offR (State.addr st) [(0, 24)]) s.mem s₅.mem := by
    rw [m₅, ← k₁₂.mem]
    rw [accList_frame] at hf₃
    exact Frame.writeOff (hf₃.offR_sub (by decide) (by decide)) (a := 0) (len := 24) (by decide) (by omega)
      (by omega) (by omega) _ rfl
  -- The words stored.
  have w : ∀ x ∈ accList, ∀ d, x.2.1 = d → x.2.2 = false →
      s₅.mem.readW (State.addr st + BitVec.ofNat 64 d) 32 = s₂.gpr x.1 := by
    intro x hx d hd hb
    have := hs₃ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    have hl : o + 4 ≤ 20 := by
      have : ∀ x ∈ accList, x.2.1 + 4 ≤ 20 := by decide
      exact this _ hx
    rw [m₅, readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]
    exact this
  refine ⟨?_, ⟨fun r hr => ?_, f₅, ?_, ?_, ?_⟩⟩
  · have e0 := w _ (by decide : (Reg.r3, 0, false) ∈ accList) 0 rfl rfl
    have e4 := w _ (by decide : (Reg.r5, 4, false) ∈ accList) 4 rfl rfl
    have e8 := w _ (by decide : (Reg.r7, 8, false) ∈ accList) 8 rfl rfl
    have e12 := w _ (by decide : (Reg.r10, 12, false) ∈ accList) 12 rfl rfl
    have e16 := w _ (by decide : (Reg.r1, 16, false) ∈ accList) 16 rfl rfl
    have e20 : s₅.mem.readW (State.addr st + BitVec.ofNat 64 20) 32 = 0 := by rw [m₅, Mem.readW_writeW_self32]
    simp only at e0 e4 e8 e12 e16
    rw [leNum_bytesAt_24, e0, e4, e8, e12, e16, e20, e3, e5, e7, e10, e1,
      show (0 : BitVec 32).toNat = 0 from rfl, val_words (fun j hj => hlL j (by omega)), hvL, hDv]
  · have hsub : ∀ r ∈ (Reg.r2 :: .r12 :: cregs), r ∈ work := by decide
    have h2 : r ≠ .r2 := by rintro rfl; exact hr (by decide)
    rw [u₅.gpr, u₄.other _ h2, hg₃]
    exact k₁₂.gpr r fun h' => hr (hsub r h')
  · rw [u₅.rd, u₄.rd, hrd₃, k₁₂.rd]
  · rw [u₅.wr, u₄.wr, hwr₃, k₁₂.wr]
  · rw [u₅.sp, u₄.sp, hsp₃, k₁₂.sp]

end

theorem accD_of_words {m m' : Mem} {B : Addr}
    (h : ∀ i < 5, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (4 * i)) 32) :
    accD m' B = accD m B := by
  have hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by simp only [hwd, h i hi]
  funext k
  simp only [accD, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega)]

/-! ## Arguments on the stack -/

theorem wp_sub {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem Fupd.keeps {s s' : State} (h : Fupd s s') (ws : List Reg) : Keeps ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp⟩

theorem wp_ldrSp {is : List Instr} {s : State} {Q : State → Prop} {t : Reg} {off : Nat} {a : Addr}
    (ho : off < 4096) (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

/-! ## The registers saved in `scratch` -/

/-- The registers `g` saved at `[0, 32)` of the scratch space at `C`. -/
def SavedS (C : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (C + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

def saveSList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 4 * i, false)

theorem saveScr_eq : saveScr = saveSList.map (storeI .r12) := rfl

/-- The scratch space's region. -/
abbrev scrR (sc : BitVec 32) : Region := ⟨State.addr sc, 128⟩

section
variable {sc : BitVec 32} (hsc : sc.toNat + 128 ≤ 2 ^ 32)
include hsc

theorem saveScr_ok {s : State} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr) :
    WP isa (.block saveScr) s fun s' => SavedS (State.addr sc) s.gpr s'.mem ∧
      Frame [⟨State.addr sc, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [saveScr_eq]
  refine WP.mono (stores_ok .r12 hsc rfl saveSList s h12 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, sub_base _ (by simp only [ssize]; omega) (by omega)⟩

theorem restoreScr_ok {s : State} {g : Reg → BitVec 32} (h12 : s.gpr .r12 = sc) (hw : scrR sc ∈ s.wr)
    (hs : SavedS (State.addr sc) g s.mem) :
    WP isa (.block restoreScr) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide +kernel
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide +kernel
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s' h => h
  refine wp_ldr (a := State.addr sc + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [hk.gpr _ (by decide), h12]; exact addr_add (by omega))
    (by rw [hk.rd, hk.wr]; exact ⟨_, List.mem_append_right _ hw, contains_off (by omega) (by omega)⟩)
    fun s1 u1 => WP.block_nil ⟨fun i hi => ?_, hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

end

/-! ## Copying bytes into the buffer -/

theorem add_ofNat_one (x : BitVec 32) (j : Nat) : x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- The buffer of the state at `B`. -/
abbrev bufR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 16⟩

/-- What copying the bytes `xs` from `src` needs, in the state `sI`: they are
readable, not in the buffer, and in memory. -/
def SrcOk (sI : State) (B : Addr) (src : BitVec 32) (xs : List Byte) : Prop :=
  ∀ i < xs.length, InRegions (sI.rd ++ sI.wr) (State.addr src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bufR B).Contains (State.addr src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (State.addr src + BitVec.ofNat 64 i) = xs.getD i 0

/-- While copying the bytes `xs` from `src` to the buffer of the state at `st`
from its byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (st src : BitVec 32) (j0 : Nat) (xs : List Byte) (j : Nat) (s : State) :
    Prop where
  j_le : j ≤ xs.length
  r5 : s.gpr .r5 = src + BitVec.ofNat 32 j
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (j0 + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (xs.length - j)
  keep : ∀ r, r ∉ [Reg.r1, .r5, .r8, .r12] → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  mem : s.mem = writeBytes sI.mem (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j)

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem copy_step {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hw : stR st ∈ sI.wr) (hS : SrcOk sI (State.addr st) src xs)
    {j : Nat} (hj : j < xs.length) {s : State} (h : CopyInv sI st src j0 xs j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI st src j0 xs (j + 1) s' ∧ s'.z = decide (xs.length - (j + 1) = 0) := by
  obtain ⟨hin, hnb, hm₀⟩ := hS j hj
  have hq : (bufR (State.addr st)).Contains (State.addr st + BitVec.ofNat 64 (56 + j0)) (xs.take j).length := by
    rw [List.length_take]
    exact contains_sub _ (by omega) (by omega) (by omega)
  have hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = xs.getD j 0 := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_ldrb (t := .r12) (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r5, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega))
    (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_strb (t := .r12) (a := State.addr st + BitVec.ofNat 64 (56 + j0 + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_assoc, ← BitVec.ofNat_add,
      show j0 + j + 56 = 56 + j0 + j by omega]; exact ea hfit (by omega))
    (by rw [u₁.wr, h.wr]; exact outSt hw (by omega)) fun s₂ m₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have hr8 : s₅.gpr .r8 = BitVec.ofNat 32 (xs.length - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r8,
      show xs.length - j = (xs.length - (j + 1)) + 1 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  refine ⟨⟨by omega, ?_, ?_, hr8, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r5,
      add_ofNat_one]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r1,
      ← Nat.add_assoc, add_ofNat_one]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.1, u₃.other _ hr.2.1, m₂.gpr, u₁.other _ hr.2.2.2]
    exact h.keep r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp, h.sp]
  · have hl : (xs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hv : (s₁.gpr .r12).setWidth 8 = xs[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hbyte]
      simp [List.getD_eq_getElem?_getD, hj]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj, Option.toList_some, writeBytes_snoc _ _ _ _ (by omega), hl, off_add]
  · rw [hz, ← u₅.gpr, hr8, ofNat_beq_zero (by omega)]

theorem copy_ok {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    (hsrc : src.toNat + xs.length ≤ 2 ^ 32) (hn : 0 < xs.length) (hw : stR st ∈ sI.wr)
    (hS : SrcOk sI (State.addr st) src xs) (h5 : sI.gpr .r5 = src)
    (h1 : sI.gpr .r1 = st + BitVec.ofNat 32 j0) (h8 : sI.gpr .r8 = BitVec.ofNat 32 xs.length) :
    WP isa copyIn sI (CopyInv sI st src j0 xs xs.length) := by
  have h₀ : CopyInv sI st src j0 xs 0 sI :=
    ⟨by omega, by rw [h5]; simp, by rw [h1, Nat.add_zero], by rw [h8, Nat.sub_zero], fun _ _ => rfl, rfl, rfl,
      rfl, by rw [List.take_zero, writeBytes_nil]⟩
  refine WP.loop (M := isa) (fun k s => ∃ j, k = xs.length - j ∧ j < xs.length ∧ CopyInv sI st src j0 xs j s)
    ?_ xs.length sI ⟨0, by omega, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hfit hj0 hsrc hw hS hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : xs.length - (j + 1) = 0
  · refine .inl ⟨by rw [eval_ne, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = xs.length by omega] at hc'
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

omit hfit in
/-- After copying: the buffer's first `j0` bytes and the bytes copied. -/
theorem CopyInv.buf {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) :
    bytesAt s.mem (State.addr st + 56) (j0 + xs.length) = bytesAt sI.mem (State.addr st + 56) j0 ++ xs := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _), ← off_add]
  exact bytesAt_writeBytes sI.mem (State.addr st + 56) j0 xs (by omega)

omit hfit in
theorem CopyInv.frame {sI : State} {src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) : Frame [bufR (State.addr st)] sI.mem s.mem := by
  rw [h.mem, List.take_of_length_le (Nat.le_refl _)]
  exact writeBytes_frame _ _ _ (contains_sub _ (by omega) (by omega) (by omega))

end

end VG.Proof.Poly1305.Arm
