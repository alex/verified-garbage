import VerifiedGarbage.Proof.Poly1305.Arm.Blocks

/-!
# Poly1305 on 32-bit ARM: the padded last block of `finalize`

Untrusted: everything here is checked by Lean. A non-empty tail is copied
into `out`, which was zeroed, a byte at a time (`copy_step`), and followed by
the byte `0x01` (`copyTail_ok`); as a number, the 16 bytes are the tail with
`0x01` appended (`padded_value`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes mac)

section
variable (s₀ : State)
/-- The tail's length, region and bytes. -/
abbrev tl : Nat := (s₀.gpr .r2).toNat
abbrev tR : Region := ⟨State.addr (s₀.gpr .r1), tl s₀⟩
abbrev tail : List Byte := bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (tl s₀)
/-- `out`. -/
abbrev oB : Addr := State.addr (s₀.gpr .r3)
abbrev oR : Region := ⟨oB s₀, 16⟩
end

/-- The precondition of `finalize`, by field. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [tR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0), oR s₀]
  st_t : (stR (s₀.gpr .r0)).Disjoint (tR s₀)
  st_o : (stR (s₀.gpr .r0)).Disjoint (oR s₀)
  t_o : (tR s₀).Disjoint (oR s₀)
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  t_fit : (s₀.gpr .r1).toNat + tl s₀ ≤ 2 ^ 32
  o_fit : (s₀.gpr .r3).toNat + 16 ≤ 2 ^ 32
  tl_lt : tl s₀ < 16

theorem FPre.of (s : State) (h : Proof.Poly1305.finalizeArm.pre s) : FPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The state `s₁` after saving the registers: `s₀` but for the saved registers. -/
structure S1 (s₀ s₁ : State) : Prop where
  gpr : s₁.gpr = s₀.gpr
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  sp : s₁.sp = s₀.sp
  frame : Frame [stR (s₀.gpr .r0)] s₀.mem s₁.mem

/-! ## Bytes -/

/-- The bytes of `out` are `f k`. -/
def OutHas (m : Mem) (O : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (O + BitVec.ofNat 64 k) = f k

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem off_ne (O : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : k ≠ j) :
    O + BitVec.ofNat 64 k ≠ O + BitVec.ofNat 64 j := by
  intro he
  have h2 : BitVec.ofNat 64 k = BitVec.ofNat 64 j := by simpa using he
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h this

theorem tail_getD {s₀ : State} {j : Nat} (hj : j < tl s₀) :
    (tail s₀).getD j 0 = s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 j) := by
  simp [tail, bytesAt, hj]

/-! ## Zeroing `out` -/

/-- After the copy's first `j` bytes, from the state `s₁`. -/
structure CInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = s₀.gpr .r1 + BitVec.ofNat 32 j
  r4 : s.gpr .r4 = s₀.gpr .r3 + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (tl s₀ - j)
  keeps : KeepsF [.r1, .r4, .r5, .r12] [oR s₀] s₁ s
  out : OutHas s.mem (oB s₀) fun k => if k < j then (tail s₀).getD k 0 else 0

theorem FPre.outW {s₀ : State} (hp : FPre s₀) {s : State} (hw : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 16) :
    InRegions s.wr (oB s₀ + BitVec.ofNat 64 d) n :=
  ⟨oR s₀, by rw [hw, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), contains_off h (by omega)⟩

theorem eaO {s₀ : State} (hp : FPre s₀) {d : Nat} (hd : d < 16) :
    State.addr (s₀.gpr .r3 + BitVec.ofNat 32 d) = oB s₀ + BitVec.ofNat 64 d :=
  addr_add (by have := hp.o_fit; omega)

theorem zero_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : S1 s₀ s₁) :
    WP isa (.block [.mov .r12 (.imm 0), .str .r12 .r3 0, .str .r12 .r3 4, .str .r12 .r3 8, .str .r12 .r3 12,
      .mov .r4 (.reg .r3), .mov .r5 (.reg .r2)]) s₁ (CInv s₀ s₁ 0) := by
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [h₁.gpr]
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_
  have hr3 : t₁.gpr .r3 = s₀.gpr .r3 := by rw [u₁.other _ (by decide), g]
  refine wp_str (a := oB s₀ + BitVec.ofNat 64 0) (by decide) (by rw [hr3]; exact eaO hp (by omega))
    (by rw [u₁.wr]; exact hp.outW h₁.wr (by omega)) fun t₂ u₂ => ?_
  refine wp_str (a := oB s₀ + BitVec.ofNat 64 4) (by decide) (by rw [u₂.gpr, hr3]; exact eaO hp (by omega))
    (by rw [u₂.wr, u₁.wr]; exact hp.outW h₁.wr (by omega)) fun t₃ u₃ => ?_
  refine wp_str (a := oB s₀ + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.gpr, u₂.gpr, hr3]; exact eaO hp (by omega))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hp.outW h₁.wr (by omega)) fun t₄ u₄ => ?_
  refine wp_str (a := oB s₀ + BitVec.ofNat 64 12) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.gpr, hr3]; exact eaO hp (by omega))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.outW h₁.wr (by omega)) fun t₅ u₅ => ?_
  refine wp_mov (op2_reg _ _) fun t₆ u₆ => wp_mov (op2_reg _ _) fun t₇ u₇ => WP.block_nil ?_
  have hz : t₁.gpr .r12 = 0 := u₁.gpr
  have e₂ : t₂.gpr = t₁.gpr := u₂.gpr
  have e₃ : t₃.gpr = t₁.gpr := u₃.gpr.trans e₂
  have e₄ : t₄.gpr = t₁.gpr := u₄.gpr.trans e₃
  have e₅ : t₅.gpr = t₁.gpr := u₅.gpr.trans e₄
  have m₅ : t₅.mem = (((s₁.mem.writeW (oB s₀ + BitVec.ofNat 64 0) (0 : BitVec 32)).writeW
      (oB s₀ + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW (oB s₀ + BitVec.ofNat 64 8) (0 : BitVec 32)).writeW
      (oB s₀ + BitVec.ofNat 64 12) (0 : BitVec 32) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, e₄, e₃, e₂, hz]
  have m₇ : t₇.mem = t₅.mem := by rw [u₇.mem, u₆.mem]
  have hw : ∀ i < 4, t₅.mem.readW (oB s₀ + BitVec.ofNat 64 (4 * i)) 32 = 0 := by
    intro i hi
    rw [m₅]
    interval_cases i
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), readW_writeW_off _ _ _ (by omega) (by omega)
        (by omega), readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), readW_writeW_off _ _ _ (by omega) (by omega)
        (by omega), Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), e₅, u₁.other _ (by decide), g]; simp
  · rw [u₇.other _ (by decide), u₆.gpr, e₅, u₁.other _ (by decide), g]; simp
  · rw [u₇.gpr, u₆.other _ (by decide), e₅, u₁.other _ (by decide), g]; simp [tl]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.2.2.1, u₆.other _ hr.2.1, e₅, u₁.other _ hr.2.2.2]
  · rw [m₇, m₅]
    have c : ∀ d, d + 4 ≤ 16 → (oR s₀).Contains (oB s₀ + BitVec.ofNat 64 d) (32 / 8) :=
      fun d hd => contains_off hd (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _ (c 8 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 12 (by omega))
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · simp only [Nat.not_lt_zero, ite_false]
    rw [m₇, show oB s₀ + BitVec.ofNat 64 k = oB s₀ + BitVec.ofNat 64 (4 * (k / 4)) + BitVec.ofNat 64 (k % 4) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod], Mem.readW_byte t₅.mem _ (Nat.mod_lt _ (by omega)),
      hw _ (by omega)]
    simp

/-! ## Copying -/

theorem succ_ofNat (x : BitVec 32) (j : Nat) : x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem copy_step {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : S1 s₀ s₁) {j : Nat} (hj : j < tl s₀)
    {s : State} (h : CInv s₀ s₁ j s) :
    WP isa (.block [.ldrb .r12 .r1 0, .strb .r12 .r4 0, .dp .add .r1 .r1 (.imm 1), .dp .add .r4 .r4 (.imm 1),
      .subs .r5 .r5 (.imm 1)]) s fun s' => CInv s₀ s₁ (j + 1) s' ∧ s'.z = decide (j + 1 = tl s₀) := by
  have htl := hp.tl_lt
  have htf := hp.t_fit
  have hof := hp.o_fit
  have hA1 : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = State.addr (s₀.gpr .r1) + BitVec.ofNat 64 j := by
    rw [h.r1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega)
  have hA4 : State.addr (s.gpr .r4 + BitVec.ofNat 32 0) = oB s₀ + BitVec.ofNat 64 j := by
    rw [h.r4, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega)
  have hrd : s.rd = s₀.rd := by rw [h.keeps.rd, h₁.rd]
  have hwr : s.wr = s₀.wr := by rw [h.keeps.wr, h₁.wr]
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 j) 1 := by
    rw [hrd, hp.rd]
    exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega) (by omega)⟩
  -- The byte copied is byte `j` of the tail.
  have hbyte : s.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 j) = (tail s₀).getD j 0 := by
    rw [tail_getD hj]
    have hf : Frame [stR (s₀.gpr .r0), oR s₀] s₀.mem s.mem :=
      (h₁.frame.mono (by simp)).trans (h.keeps.frame.mono (by simp))
    refine hf.bytes (R := tR s₀) (fun r hr => ?_) (by show tl s₀ ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_t.symm
    · exact hp.t_o
  refine wp_ldrb (by decide) hA1 hin fun t₁ u₁ => ?_
  refine wp_strb (a := oB s₀ + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide)]; exact hA4)
    (by rw [u₁.wr, hwr]; exact hp.outW rfl (by omega)) fun t₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun t₅ u₅ hz => WP.block_nil ⟨⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩,
    fun k hk => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r1]
    exact succ_ofNat _ _
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r4]
    exact succ_ofNat _ _
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r5,
      show tl s₀ - j = (tl s₀ - (j + 1)) + 1 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.gpr, u₁.other _ hr.2.2.2]
    exact h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact h.keeps.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.keeps.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.keeps.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.keeps.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₁.gpr, writeW8_apply]
    dsimp only
    by_cases hkj : k = j
    · subst hkj
      rw [iteT rfl, iteT (by omega), BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hbyte]
    · rw [iteF (off_ne _ (by omega) (by omega) hkj), h.out k hk]
      dsimp only
      by_cases hk' : k < j
      · rw [iteT hk', iteT (by omega)]
      · rw [iteF hk', iteF (by omega)]
  · have e : t₄.gpr .r5 = BitVec.ofNat 32 (tl s₀ - j) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r5]
    rw [hz, e, show tl s₀ - j = (tl s₀ - (j + 1)) + 1 by omega, BitVec.ofNat_add,
      show ∀ x : BitVec 32, x + BitVec.ofNat 32 1 - 1 = x from fun x => BitVec.add_sub_cancel _ _,
      ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]
    omega

/-- The padded block: the tail, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < tl s₀ then (tail s₀).getD k 0 else if k = tl s₀ then 1 else 0

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : S1 s₀ s₁) {s : State}
    (h : CInv s₀ s₁ (tl s₀) s) :
    WP isa (.block [.mov .r12 (.imm 1), .strb .r12 .r4 0]) s fun s' =>
      KeepsF [.r1, .r4, .r5, .r12] [oR s₀] s₁ s' ∧ OutHas s'.mem (oB s₀) (padded s₀) := by
  have htl := hp.tl_lt
  have hof := hp.o_fit
  have hA4 : State.addr (s.gpr .r4 + BitVec.ofNat 32 0) = oB s₀ + BitVec.ofNat 64 (tl s₀) := by
    rw [h.r4, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero]; exact addr_add (by omega)
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_
  refine wp_strb (a := oB s₀ + BitVec.ofNat 64 (tl s₀)) (by decide) (by rw [u₁.other _ (by decide)]; exact hA4)
    (by rw [u₁.wr, h.keeps.wr, h₁.wr]; exact hp.outW rfl (by omega)) fun t₂ u₂ =>
      WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.gpr, u₁.other _ hr.2.2.2]; exact h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · rw [u₂.mem, u₁.mem]
    exact h.keeps.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · rw [u₂.rd, u₁.rd, h.keeps.rd]
  · rw [u₂.wr, u₁.wr, h.keeps.wr]
  · rw [u₂.sp, u₁.sp, h.keeps.sp]
  · rw [u₂.mem, u₁.mem, u₁.gpr, writeW8_apply]
    by_cases hkj : k = tl s₀
    · subst hkj
      rw [iteT rfl, padded, iteF (by omega), iteT rfl]
      rfl
    · rw [iteF (off_ne _ (by omega) (by omega) hkj), h.out k hk, padded, iteF hkj]

/-- The padded block as a number: the tail with `0x01` appended. -/
theorem padded_value {s₀ : State} (hp : FPre s₀) {m : Mem} (h : OutHas m (oB s₀) (padded s₀)) :
    leNum (bytesAt m (oB s₀) 16) = leNum (tail s₀ ++ [0x01]) := by
  have htl := hp.tl_lt
  have hl : bytesAt m (oB s₀) 16 = (tail s₀ ++ [0x01]) ++ List.replicate (15 - tl s₀) 0 := by
    have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
    apply List.ext_getElem
    · simp [hlen, Poly1305.length_bytesAt]; omega
    · intro k h₁ h₂
      rw [Poly1305.length_bytesAt] at h₁
      have e : (bytesAt m (oB s₀) 16)[k] = padded s₀ k := by
        simp only [bytesAt, List.getElem_map, List.getElem_range]; exact h k h₁
      have hl1 : (tail s₀ ++ [0x01]).length = tl s₀ + 1 := by
        rw [List.length_append, hlen, List.length_singleton]
      refine e.trans ?_
      rw [padded]
      rcases Nat.lt_trichotomy k (tl s₀) with hk | rfl | hk
      · have a1 : k < (tail s₀ ++ [0x01]).length := by rw [hl1]; omega
        have a2 : k < (tail s₀).length := by rw [hlen]; omega
        rw [List.getElem_append_left a1, List.getElem_append_left a2, iteT hk]
        simp [a2]
      · have a1 : tl s₀ < (tail s₀ ++ [0x01]).length := by rw [hl1]; omega
        have a2 : (tail s₀).length ≤ tl s₀ := by rw [hlen]
        rw [List.getElem_append_left a1, List.getElem_append_right a2, iteF (by omega), iteT rfl]
        simp [hlen]
      · have a1 : (tail s₀ ++ [0x01]).length ≤ k := by rw [hl1]; omega
        rw [List.getElem_append_right a1, iteF (by omega), iteF (by omega)]
        simp
  rw [hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

theorem copyTail_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : S1 s₀ s₁) (hpos : 0 < tl s₀) :
    WP isa copyTail s₁ fun s =>
      KeepsF [.r1, .r4, .r5, .r12] [oR s₀] s₁ s ∧ OutHas s.mem (oB s₀) (padded s₀) := by
  refine WP.seq (WP.mono (zero_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := CInv s₀ s₁ (tl s₀)) ?_ fun s₃ h₃ => pad1_ok hp h₁ h₃)
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tl s₀ - j ∧ j < tl s₀ ∧ CInv s₀ s₁ j s) ?_ (tl s₀) s₂
    ⟨0, rfl, hpos, h₂⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (copy_step hp h₁ hj h) fun s' ⟨h', hz⟩ => ?_
  by_cases hl : j + 1 = tl s₀
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hl], tl s₀ - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

end VG.Proof.Poly1305.Arm
