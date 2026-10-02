import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS
import VerifiedGarbage.Proof.Poly1305.AArch64.Buffer
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on AArch64: `finalize`
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64 VG.Proof.Poly1305.AArch64
open VG.Impl.Poly1305.AArch64 (zeroBody)
open VG.Impl.Poly1305.AArch64.Radix64
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

theorem kf_lt (s₀ : State) : kf s₀ < 16 := Nat.mod_lt _ (by decide)

/-! ## Prologue -/

/-- The state after the prologue, with the memory `m₁` it leaves. -/
structure F0 (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x2 : s.gpr .x2 = BitVec.ofNat 64 (kf s₀)
  x3 : s.gpr .x3 = op s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  frame : Frame [cR (st s₀)] s₀.mem m₁
  acc : A0 s₀ < P → hval s = A0 s₀ ∧ Bounds s

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x2 15 0, .logic .and .x .x2 .x1 .x2] : List Instr) ++ setup)) s₀
      fun s => F0 s₀ s.mem s := by
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_and fun s₃ u₃ =>
    WP.block_nil ?_)
  have x0₃ : s₃.gpr .x0 = st s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s₀.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (setup_ok s₃ (by rw [u₃.wr, u₂.wr, u₁.wr, x0₃]; exact hp.st_in)) fun s h => ?_
  obtain ⟨hk, ha, k⟩ := h
  rw [x0₃, m₃] at hk
  simp only [A0, x0₃, m₃] at ha
  exact ⟨by rw [k.gpr' (r := .x0), x0₃],
    by rw [k.gpr' (r := .x2), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), and15],
    by rw [k.gpr' (r := .x3), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, add_ofNat_zero],
    hk, by rw [k.2.2.1, u₃.rd, u₂.rd, u₁.rd], by rw [k.2.2.2, u₃.wr, u₂.wr, u₁.wr], rfl,
    by rw [k.2.1, m₃]; exact Frame.refl _ _, ha⟩

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
  exact Offset.disjoint (st s₀) (d := 56 + k) (n := 1) (by omega_using [hk, hkl]) (by omega_using [hk, hkl]) (by decide) _
    (Region.contains_self _ _) hc

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
  refine ⟨⟨(Nat.le_refl _), Nat.le_of_lt hk⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr],
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, h₁.mem]; exact Frame.refl _ _), fun k hk' => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₂.other _ (by decide), h₁.x0, h₁.x2]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.x2,
      show (16 : BitVec 16).setWidth 64 = BitVec.ofNat 64 16 by decide, sub_ofNat (by omega_using [hk])]
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
  refine ⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [u₄.rd, u₃.rd, m₂.rd, h.rd], by rw [u₄.wr, u₃.wr, m₂.wr, h.wr], ?_, fun k hk => ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.x9, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.x10, show BitVec.ofNat 64 1 = 1 from rfl,
      ofNat_pred (by omega_using [hj]), Nat.sub_sub]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.x11]
  · rw [u₄.other r h2, u₃.other r h1, m₂.gpr, h.keep r h1 h2 h3]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega_using [hj]))
  · rw [u₄.mem, u₃.mem, m₂.mem, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.x11, show ¬ k < kf s₀ by have := h.j_le.1; omega_using [this],
        show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]

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
      !(BitVec.ofNat 64 (16 - (j + 1)) == 0) from rfl, ofNat_beq_zero (by omega_using [hj])]
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [hev]; simp; omega_using [hj, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

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
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bufB_eq]; exact bfR_contains _ (by omega_using [hk]))
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
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (tail s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kf s₀ by omega_using [hlen, hk'], show k ≠ kf s₀ by omega_using [hlen, hk']]
  rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.x0, .x3, .x7, .x8, .x17], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  acc : A0 s₀ < P → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧ Bounds s

theorem tail_nil {s₀ : State} (h : kf s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_eq : lastBlock =
    .seq (.block [.movz .x .x11 0 0, .add .x .x9 .x0 .x2, .movz .x .x10 16 0, .sub .x .x10 .x10 .x2])
      (.seq (.loop (.block zeroBody) (.nonzero .x .x10))
        (.block (([.movz .x .x11 1 0, .add .x .x9 .x0 .x2, .strb .x11 .x9 56] : List Instr) ++
          (([.addImm .x .x1 .x0 56] : List Instr) ++ absorb false)))) := rfl

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁)
    (hpos : 0 < kf s₀) : WP isa lastBlock s₁ (Tail s₀ m₁ s₁) := by
  have hk := kf_lt s₀
  rw [lastBlock_eq]
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₄.gpr r = s₁.gpr r := h₄.keep
  have x0₄ : s₄.gpr .x0 = st s₀ := by rw [g .x0 (by decide) (by decide) (by decide), h₁.x0]
  refine WP.mono (absorbBuf_ok s₄ false
    (h₁.keys.of_regs fun r hr => g r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert))
    (by rw [h₄.wr, x0₄]; exact hp.st_in)) fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr],
    by rw [k₅.2.1]; exact h₄.frame, fun hA => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [k₅.gpr', g _ (by decide) (by decide) (by decide)]
  · obtain ⟨hv₄, hb₄⟩ := bounds_eq (s := s₁) (s' := s₄) (fun r hr => g r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert))
    obtain ⟨hv₁, hb₁⟩ := h₁.acc hA
    obtain ⟨hv, hb⟩ := ha (hb₄ hb₁)
    refine ⟨?_, hb⟩
    have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv₄, hv₁, x0₄, padded_value h₄.buf, Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen]),
      Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

set_option simprocs false in
/-- Storing the tag. -/
theorem storeTag_ok (s : State) (hout : (⟨s.gpr .x3, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block storeTag) s fun s' =>
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 64 = s.gpr .x4 ∧
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 8) 64 = s.gpr .x5 ∧
      Frame [⟨s.gpr .x3, 16⟩] s.mem s'.mem := by
  have o0 : InRegions s.wr (off (s.gpr .x3) 0) 8 := ⟨_, hout, contains_off (by decide) (by decide)⟩
  have o8 : InRegions s.wr (off (s.gpr .x3) 8) 8 := ⟨_, hout, contains_off (by decide) (by decide)⟩
  simp only [off] at o0 o8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeTag, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    o8, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_⟩
  · have := readW_writeW_off (s.mem.writeW (off (s.gpr .x3) 0) (s.gpr .x4)) (s.gpr .x3) (s.gpr .x5)
      (d := 0) (e := 8) (by decide) (by decide) (by decide)
    simp only [off] at this
    rw [this, Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))

/-- A key word, unchanged since entry. -/
theorem key_word {s₀ : State} {m : Mem} (hf : Frame [cR (st s₀), bfR (st s₀)] s₀.mem m) {d : Nat}
    (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 56) : m.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine hf.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> exact Offset.disjoint (st s₀) (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂]) (by decide)

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : F0 s₀ m₁ s₁) {s : State}
    (ht : Tail s₀ m₁ s₁ s) :
    WP isa (.block (reduce ++ addS ++ storeTag)) s fun s' =>
      Proof.Poly1305.finalizeAArch64.post s₀ s' := by
  have x0 : s.gpr .x0 = st s₀ := by rw [ht.keep .x0 (by simp), h₁.x0]
  have x3 : s.gpr .x3 = op s₀ := by rw [ht.keep .x3 (by simp), h₁.x3]
  have hf : Frame [cR (st s₀), bfR (st s₀)] s₀.mem s.mem :=
    (h₁.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (addS_ok s₂ (by
    rw [k₂.2.2.2, ht.wr, k₂.gpr', x0]; exact hp.st_in)) fun s₃ ⟨hsum, k₃⟩ => ?_)
  have k₂₃ := k₂.trans k₃
  refine WP.mono (storeTag_ok s₃ (by
    rw [k₂₃.2.2.2, k₂₃.gpr', ht.wr, x3]; exact hp.o_in))
    fun s₇ ⟨t0, t8, _⟩ => ?_
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kf s₀ = (W ++ B).length % 16 := hcnt
  have htail : tail s₀ = B := by rw [tail, hk, off_56]; exact hBb
  rw [← htail]
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := ht.acc hA
  have hN := hr hb
  have ks40 := key_word hf (d := 40) (by decide) (by decide)
  have ks48 := key_word hf (d := 48) (by decide) (by decide)
  rw [k₂.2.1, k₂.gpr' (r := .x0), x0, ks40, ks48] at hsum
  have hn : ((s₂.gpr .x4).toNat + 2 ^ 64 * (s₂.gpr .x5).toNat) % 2 ^ 128 = hval s₂ % 2 ^ 128 := by
    simp only [hval]
    omega_using []
  have hsum' : (s₃.gpr .x4).toNat + 2 ^ 64 * (s₃.gpr .x5).toNat =
      (Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) +
        w64 s₀.mem (off (st s₀) 40) 0 + 2 ^ 64 * w64 s₀.mem (off (st s₀) 40) 8) % 2 ^ 128 := by
    have hv₂ : hval s₂ = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) := by
      rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    have w40 : w64 s₀.mem (off (st s₀) 40) 0 =
        (s₀.mem.readW (off (st s₀) 40) 64).toNat := by simp only [w64, off, BitVec.add_zero]
    have w48 : w64 s₀.mem (off (st s₀) 40) 8 =
        (s₀.mem.readW (off (st s₀) 48) 64).toNat := by
      simp only [w64, off, Offset.add_add]
    rw [w40, w48]
    omega_using [hsum, hn, hv₂]
  have x3₃ : s₃.gpr .x3 = op s₀ := by rw [k₂₃.gpr', x3]
  rw [x3₃, add_ofNat_zero] at t0
  rw [x3₃] at t8
  simp only [Spec.Poly1305.mac]
  rw [← repr_key hrep, clamp_key, key_drop, leNum_key, Poly1305.accumulate_append hrep.1,
    repr_acc hrep, ← Poly1305.leBytes_mod 16]
  simp only [Rn, Nat.add_assoc] at hsum'
  change bytesAt s₇.mem (op s₀) 16 = leBytes 16
    ((Poly1305.absorbAll (Rk s₀.mem (st s₀)) (A0 s₀) (tail s₀) +
      (w64 s₀.mem (off (st s₀) 40) 0 + 2 ^ 64 * w64 s₀.mem (off (st s₀) 40) 8)) % 2 ^ 128)
  refine Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [t0]
    have lo := (s₃.gpr .x4).isLt
    have hi := (s₃.gpr .x5).isLt
    omega_using [hsum', lo, hi]
  · rw [t8]
    have lo := (s₃.gpr .x4).isLt
    have hi := (s₃.gpr .x5).isLt
    omega_using [hsum', lo, hi]

/-! ## The whole function -/

theorem finalize_eq : finalize =
    .seq (.block (([.addImm .x .x3 .x2 0, .movz .x .x2 15 0, .logic .and .x .x2 .x1 .x2] : List Instr) ++ setup))
      (.seq (.ite (.zero .x .x2) (.block []) lastBlock) (.block (reduce ++ addS ++ storeTag))) := rfl

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ (Proof.Poly1305.finalizeAArch64.post s₀) := by
  rw [finalize_eq]
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ s₁.mem s₁) ?_ fun s₂ h₂ => fepilogue_ok hp h₁ h₂)
  refine WP.ite (decide (kf s₀ = 0))
    (by rw [eval_zero, h₁.x2, ofNat_beq_zero (by have := kf_lt s₀; omega_using [this])]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, Frame.refl _ _, fun hA => ?_⟩
    obtain ⟨e, b⟩ := h₁.acc hA
    refine ⟨?_, b⟩
    rw [tail_nil h, Poly1305.absorbAll_nil, e]
  · simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp h₁ (Nat.pos_of_ne_zero h)

def finalizeSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x3000 | .x3 => 0x5000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩, ⟨0x5000, 128⟩]

theorem finalize_untouched : Untouched Impl.Poly1305.AArch64.Radix64.finalize :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.Radix64.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.finalizeAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := finalize_correct (FPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (finalize_untouched r hr) he, Exec.sp he, Exec.preservedV he⟩, h⟩

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeAArch64.pre
    Proof.Poly1305.finalizeAArch64.pub Impl.Poly1305.AArch64.Radix64.finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem finalize_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.Radix64.finalize (Spec.Poly1305.finalizeContract
      AArch64.abi) :=
  Verified.of_correct finalize_ok finalize_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, AArch64.abi,
          AArch64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Proof.Poly1305.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig, AArch64.abi,
          AArch64.argRegs, Proof.Poly1305.AArch64.Radix64.finalizeSat]
          [Proof.Poly1305.AArch64.Radix64.finalizeSat] using Proof.Poly1305.AArch64.Radix64.finalizeSat }

end VG.Proof.Poly1305.AArch64.Radix64
