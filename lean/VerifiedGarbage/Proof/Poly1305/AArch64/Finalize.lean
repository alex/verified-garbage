import VerifiedGarbage.Proof.Poly1305.AArch64.Buffer

/-!
# Poly1305 on AArch64: `finalize`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

/-- The bytes of the buffer, as read from memory. -/
theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 56) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  rw [← h k (List.mem_range.mp hk), bufB_eq]

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The number of bytes buffered. -/
abbrev kf : Nat := (s₀.gpr .x1).toNat % 16
abbrev op : Addr := s₀.gpr .x2
abbrev oR : Region := ⟨op s₀, 16⟩
/-- The bytes buffered. -/
abbrev tail : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kf s₀)
end

structure FPre (s₀ : State) : Prop where
  st_in : sR (st s₀) ∈ s₀.wr
  o_in : oR s₀ ∈ s₀.wr
  st_o : (sR (st s₀)).Disjoint (oR s₀)

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeAArch64.pre s₀) : FPre s₀ :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem kf_lt (s₀ : State) : kf s₀ < 16 := Nat.mod_lt _ (by omega)

/-! ## Prologue -/

/-- The state after the prologue, with the memory `m₁` it leaves. -/
structure F0 (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x2 : s.gpr .x2 = BitVec.ofNat 64 (kf s₀)
  x3 : s.gpr .x3 = op s₀
  mask : s.gpr .x17 = M26
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  frame : Frame [cR (st s₀)] s₀.mem m₁
  coefs : Coefs m₁ (st s₀) (Rn s₀)
  acc : A0 s₀ < P → hv s = A0 s₀ ∧ Bounds s

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block ([.addImm .x .x3 .x2 0, .movz .x .x2 15 0, .logic .and .x .x2 .x1 .x2] ++ setup)) s₀
      fun s => F0 s₀ s.mem s := by
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_and fun s₃ u₃ =>
    WP.block_nil ?_)
  have x0₃ : s₃.gpr .x0 = st s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s₀.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (setup_ok s₃ (by rw [u₃.wr, u₂.wr, u₁.wr, x0₃]; exact hp.st_in)) fun s h => ?_
  have hf := h.frame; have hc := h.coefs; have ha := h.acc
  rw [x0₃, m₃] at hf hc ha
  exact ⟨by rw [h.gpr .x0 (by decide), x0₃],
    by rw [h.gpr .x2 (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), and15],
    by rw [h.gpr .x3 (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, add_ofNat_zero],
    h.mask, by rw [h.rd, u₃.rd, u₂.rd, u₁.rd], by rw [h.wr, u₃.wr, u₂.wr, u₁.wr], rfl, hf, hc, ha⟩

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kf s₀ then (tail s₀).getD k 0 else if k = kf s₀ then 1 else 0

/-- The buffered bytes in the memory the prologue leaves. -/
theorem F0.tail {s₀ : State} {m₁ : Mem} {s₁ : State} (h : F0 s₀ m₁ s₁) {k : Nat} (hk : k < kf s₀) :
    m₁ (bufB (st s₀) k) = (tail s₀).getD k 0 := by
  have hkl := kf_lt s₀
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [← bufB_eq]
  refine h.frame _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains, off, bufB] at hc
  bv_omega

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZInv (s₀ : State) (m₁ : Mem) (s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kf s₀ ≤ j ∧ j ≤ 16
  x9 : s.gpr .x9 = st s₀ + BitVec.ofNat 64 j
  x10 : s.gpr .x10 = BitVec.ofNat 64 (16 - j)
  x11 : s.gpr .x11 = 0
  keep : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) fun k =>
    if k < kf s₀ then (tail s₀).getD k 0 else if k < j then 0 else m₁ (bufB (st s₀) k)

theorem zinit_ok {s₀ : State} {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) :
    WP isa (.block [.movz .x .x11 0 0, .add .x .x9 .x0 .x2, .movz .x .x10 16 0, .sub .x .x10 .x10 .x2]) s₁
      (ZInv s₀ m₁ s₁ (kf s₀)) := by
  have hk := kf_lt s₀
  refine wp_movz fun s₂ u₂ => wp_add fun s₃ u₃ => wp_movz fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  refine ⟨⟨le_rfl, hk.le⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr],
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, h₁.mem]; exact Frame.refl _ _), fun k hk' => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₂.other _ (by decide), h₁.x0, h₁.x2]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.x2,
      show (16 : BitVec 16).setWidth 64 = BitVec.ofNat 64 16 by decide, sub_ofNat (by omega)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  · rw [u₅.other r h2, u₄.other r h2, u₃.other r h1, u₂.other r h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, h₁.mem]
    by_cases hkf : k < kf s₀
    · simp only [hkf, ite_true]; exact h₁.tail hkf
    · simp only [hkf, ite_false]

theorem zero_step {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} {j : Nat}
    (hj : j < 16) {s : State} (h : ZInv s₀ m₁ s₁ j s) :
    WP isa (.block zeroBody) s fun s' => ZInv s₀ m₁ s₁ (j + 1) s' := by
  refine wp_strb (t := .x11) (a := bufB (st s₀) j) (by decide) (by rw [h.x9, bufB_of])
    (by rw [h.wr]; exact bufB_in hp.st_in hj) fun s₂ m₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_subImm (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨⟨h.j_le.1.trans (Nat.le_succ _), by omega⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [u₄.rd, u₃.rd, m₂.rd, h.rd], by rw [u₄.wr, u₃.wr, m₂.wr, h.wr], ?_, fun k hk => ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.x9, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.x10, show BitVec.ofNat 64 1 = 1 from rfl,
      ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.x11]
  · rw [u₄.other r h2, u₃.other r h1, m₂.gpr, h.keep r h1 h2 h3]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega))
  · rw [u₄.mem, u₃.mem, m₂.mem, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.x11, show ¬ k < kf s₀ by have := h.j_le.1; omega,
        show k < k + 1 by omega, ite_false]
      rfl
    · simp only [bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega]

theorem zeroLoop_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} {s : State}
    (h : ZInv s₀ m₁ s₁ (kf s₀) s) :
    WP isa (.loop (.block zeroBody) (.nonzero .x .x10)) s (ZInv s₀ m₁ s₁ 16) := by
  have hk := kf_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ m₁ s₁ j s) ?_ _ s
    ⟨kf s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp hj hz) fun s' h' => ?_
  have hev : isa.eval (.nonzero .x .x10) s' = some (!decide (16 - (j + 1) = 0)) := by
    rw [eval_nonzero, h'.x10, show (BitVec.ofNat 64 (16 - (j + 1)) != 0) =
      !(BitVec.ofNat 64 (16 - (j + 1)) == 0) from rfl, ofNat_beq_zero (by omega)]
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, _, by omega, j + 1, rfl, by omega, h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem one_byte : (((1 : BitVec 16).setWidth 64).setWidth 8 : Byte) = 1 := by decide

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (h : ZInv s₀ m₁ s₁ 16 s) :
    WP isa (.block [.movz .x .x11 1 0, .add .x .x9 .x0 .x2, .strb .x11 .x9 56]) s (PInv s₀ m₁ s₁) := by
  have hk := kf_lt s₀
  refine wp_movz fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have hx9 : s₃.gpr .x9 = st s₀ + BitVec.ofNat 64 (kf s₀) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), h.keep _ (by decide) (by decide)
      (by decide), h.keep _ (by decide) (by decide) (by decide), h₁.x0, h₁.x2]
  refine wp_strb (t := .x11) (a := bufB (st s₀) (kf s₀)) (by decide) (by rw [hx9, bufB_of])
    (by rw [u₃.wr, u₂.wr, h.wr]; exact bufB_in hp.st_in hk) fun s₄ m₄ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, by rw [m₄.rd, u₃.rd, u₂.rd, h.rd], by rw [m₄.wr, u₃.wr, u₂.wr, h.wr], ?_,
    fun k hk' => ?_⟩
  · rw [m₄.gpr, u₃.other r h1, u₂.other r h3, h.keep r h1 h2 h3]
  · rw [m₄.mem, u₃.mem, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega))
  · rw [m₄.mem, u₃.mem, u₂.mem, writeW8_apply, u₃.other _ (by decide), u₂.gpr, one_byte]
    by_cases hkj : k = kf s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
    · simp only [bufB_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true, padded]
      · simp only [h1, ite_false, hk', ite_true, padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    leNum (bytesAt m (off (st s₀) 56) 16) + 2 ^ 128 * false.toNat = leNum (tail s₀ ++ [0x01]) := by
  have hk := kf_lt s₀
  have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (padded s₀) = (tail s₀ ++ [0x01]) ++ List.replicate (15 - kf s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_append_left (by omega)]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (tail s₀).length by omega)]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega)]
        simp [padded, show ¬ k < kf s₀ by omega, show k ≠ kf s₀ by omega]
  rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.x0, .x3, .x17], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧ Bounds s

theorem tail_nil {s₀ : State} (h : kf s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_eq : lastBlock =
    .seq (.block [.movz .x .x11 0 0, .add .x .x9 .x0 .x2, .movz .x .x10 16 0, .sub .x .x10 .x10 .x2])
      (.seq (.loop (.block zeroBody) (.nonzero .x .x10))
        (.block ([.movz .x .x11 1 0, .add .x .x9 .x0 .x2, .strb .x11 .x9 56] ++
          ([.addImm .x .x1 .x0 56] ++ absorb false)))) := rfl

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁)
    (hpos : 0 < kf s₀) : WP isa lastBlock s₁ (Tail s₀ m₁ s₁) := by
  have hk := kf_lt s₀
  rw [lastBlock_eq]
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₄.gpr r = s₁.gpr r := h₄.keep
  have x0₄ : s₄.gpr .x0 = st s₀ := by rw [g .x0 (by decide) (by decide) (by decide), h₁.x0]
  have hco : Coefs s₄.mem (s₄.gpr .x0) (Rn s₀) := by
    rw [x0₄]; exact h₁.coefs.frame h₄.frame
  refine WP.mono (absorbBuf_ok s₄ false (Rk_lt _ _)
    (by rw [g .x17 (by decide) (by decide) (by decide)]; exact h₁.mask) hco
    (by rw [h₄.wr, x0₄]; exact hp.st_in)) fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr],
    by rw [k₅.2.1]; exact h₄.frame, fun hA => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [k₅.gpr', g _ (by decide) (by decide) (by decide)]
  · obtain ⟨hv₄, hb₄⟩ := bounds_eq (s := s₁) (s' := s₄) (fun r hr => g r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert))
    obtain ⟨hv₁, hb₁⟩ := h₁.acc hA
    obtain ⟨hv, hb⟩ := ha (hb₄ hb₁)
    refine ⟨?_, hb⟩
    have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv₄, hv₁, x0₄, padded_value h₄.buf, Poly1305.absorbAll_block (by omega) (by omega),
      Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

set_option simprocs false in
/-- Storing the tag. -/
theorem storeTag_ok (s : State) (hout : (⟨s.gpr .x3, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block storeTag) s fun s' =>
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 64 = s.gpr .x14 ∧
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 8) 64 = s.gpr .x15 ∧
      Frame [⟨s.gpr .x3, 16⟩] s.mem s'.mem := by
  have o0 : InRegions s.wr (off (s.gpr .x3) 0) 8 := ⟨_, hout, contains_off (by omega) (by omega)⟩
  have o8 : InRegions s.wr (off (s.gpr .x3) 8) 8 := ⟨_, hout, contains_off (by omega) (by omega)⟩
  simp only [off] at o0 o8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeTag, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    o8, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_⟩
  · have := readW_writeW_off (s.mem.writeW (off (s.gpr .x3) 0) (s.gpr .x14)) (s.gpr .x3) (s.gpr .x15)
      (d := 0) (e := 8) (by omega) (by omega) (by omega)
    simp only [off] at this
    rw [this, Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem fepi_eq : reduce ++ addS ++ pack ++ storeTag = reduce ++ (load2 .x0 40 ++ (split ++
    ((addLimbs ++ carryStep .x4 .x4 .x5 ++ normalize) ++ (pack ++ storeTag)))) := by
  simp only [addS, List.append_assoc]

/-- A key word, unchanged since entry. -/
theorem key_word {s₀ : State} {m : Mem} (hf : Frame [cR (st s₀), bfR (st s₀)] s₀.mem m) {d : Nat}
    (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 56) : m.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine hf.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> intro a h₁ h₂ <;> simp only [Region.Contains, off] at h₁ h₂ <;> bv_omega

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (ht : Tail s₀ m₁ s₁ s) :
    WP isa (.block (reduce ++ addS ++ pack ++ storeTag)) s fun s' =>
      Proof.Poly1305.finalizeAArch64.post s₀ s' := by
  have hm : s.gpr .x17 = M26 := by rw [ht.keep .x17 (by simp)]; exact h₁.mask
  have x0 : s.gpr .x0 = st s₀ := by rw [ht.keep .x0 (by simp), h₁.x0]
  have x3 : s.gpr .x3 = op s₀ := by rw [ht.keep .x3 (by simp), h₁.x3]
  have hf : Frame [cR (st s₀), bfR (st s₀)] s₀.mem s.mem :=
    (h₁.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  rw [fepi_eq]
  refine WP.block_append (WP.mono (reduce_ok s hm) fun s₂ ⟨hr, k₂⟩ => ?_)
  have hin : ∀ d, d + 8 ≤ 128 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [k₂.2.2.1, k₂.2.2.2, k₂.gpr', ht.rd, ht.wr, x0]
    exact ⟨_, List.mem_append_right _ hp.st_in, contains_off hd (by omega)⟩
  refine WP.block_append (WP.mono (load2_ok s₂ (n := .x0) (off := 40) (by decide) (by decide)
    (by decide) (hin 40 (by omega)) (hin (40 + 8) (by omega))) fun s₃ ⟨l₁, l₂, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₃ (by rw [k₃.gpr', k₂.gpr']; exact hm))
    fun s₄ ⟨m0, m1, m2, m3, m4, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (addCarry_ok s₄ (by rw [k₄.gpr', k₃.gpr', k₂.gpr']; exact hm))
    fun s₅ ⟨ha, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (pack_ok s₅) fun s₆ ⟨hq, k₆⟩ => ?_)
  have k₂₆ := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  refine WP.mono (storeTag_ok s₆ (by
    rw [k₂₆.2.2.2, k₂₆.gpr', ht.wr, x3]; exact hp.o_in))
    fun s₇ ⟨t0, t8, _⟩ => ?_
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kf s₀ = (W ++ B).length % 16 := hcnt
  have htail : tail s₀ = B := by rw [tail, hk, off_56]; exact hBb
  rw [← htail]
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := ht.acc hA
  obtain ⟨hN, n0, n1, n2, n3, n4⟩ := hr hb
  -- The limbs of `h mod p`, in `s₄`.
  have k₃₄ := k₃.trans k₄
  have e4 : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s₄ r = v s₂ r := fun r hr => by
    simp only [v]; rw [k₃₄.1 r (by revert hr; decide +revert)]
  rw [← e4 .x4 (by simp), ← e4 .x5 (by simp), ← e4 .x6 (by simp), ← e4 .x7 (by simp),
    ← e4 .x8 (by simp)] at hN
  rw [← e4 .x4 (by simp)] at n0; rw [← e4 .x5 (by simp)] at n1; rw [← e4 .x6 (by simp)] at n2
  rw [← e4 .x7 (by simp)] at n3; rw [← e4 .x8 (by simp)] at n4
  -- The key's `s`.
  have hS : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 =
      w64 s₀.mem (off (st s₀) 40) 0 + 2 ^ 64 * w64 s₀.mem (off (st s₀) 40) 8 := by
    simp only [v, w64, l₁, l₂, k₂.2.1, k₂.gpr' (r := .x0), x0, off, add_ofNat_zero, add_ofNat_add]
    rw [key_word hf (d := 40) (by omega) (by omega), key_word hf (d := 40 + 8) (by omega) (by omega)]
  have hSlt : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 < 2 ^ 128 := by
    have := (s₃.gpr .x14).isLt; have := (s₃.gpr .x15).isLt; simp only [v]; omega
  have hsum := ha (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [m0]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m1]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m2]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m3]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m4]; exact lt_trans (lim4_lt hSlt) (by norm_num))
  obtain ⟨hV, b0, b1, b2, b3, -⟩ := hsum
  rw [m0, m1, m2, m3, m4, val5_lim, hS, hN, hv₀,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)] at hV
  obtain ⟨q0, q1, -⟩ := hq b0 b1 b2 b3
  rw [hV] at q0 q1
  have x3₆ : s₆.gpr .x3 = op s₀ := by rw [k₂₆.gpr', x3]
  rw [x3₆, add_ofNat_zero] at t0
  rw [x3₆] at t8
  simp only [Spec.Poly1305.mac]
  rw [← repr_key hrep, clamp_key, key_drop, leNum_key, Poly1305.accumulate_append hrep.1,
    repr_acc hrep]
  refine Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [t0]; exact q0
  · rw [t8]; exact q1

/-! ## The whole function -/

theorem finalize_eq : finalize =
    .seq (.block ([.addImm .x .x3 .x2 0, .movz .x .x2 15 0, .logic .and .x .x2 .x1 .x2] ++ setup))
      (.seq (.ite (.zero .x .x2) (.block []) lastBlock) (.block (reduce ++ addS ++ pack ++ storeTag))) := rfl

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ (Proof.Poly1305.finalizeAArch64.post s₀) := by
  rw [finalize_eq]
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ s₁.mem s₁) ?_ fun s₂ h₂ => fepilogue_ok hp h₁ h₂)
  refine WP.ite (decide (kf s₀ = 0))
    (by rw [eval_zero, h₁.x2, ofNat_beq_zero (by have := kf_lt s₀; omega)]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, Frame.refl _ _, fun hA => ?_⟩
    obtain ⟨e, b⟩ := h₁.acc hA
    refine ⟨?_, b⟩
    rw [tail_nil h, Poly1305.absorbAll_nil, e]
  · simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp h₁ (Nat.pos_of_ne_zero h)

/-- A state satisfying the precondition (with 128 bytes of working space at `x3`). -/
def finalizeSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x3000 | .x3 => 0x5000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩, ⟨0x5000, 128⟩]

theorem finalize_untouched : Untouched Impl.Poly1305.AArch64.finalize :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem finalize_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.finalize Proof.Poly1305.finalizeAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := finalize_correct (FPre.of s hs)
    exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (finalize_untouched r hr) he, Exec.sp he⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · refine ⟨finalizeSat, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    intro a h₁ h₂
    simp only [Region.Contains, finalizeSat] at h₁ h₂
    bv_omega

end VG.Proof.Poly1305.AArch64
