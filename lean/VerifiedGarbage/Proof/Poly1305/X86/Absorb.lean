import VerifiedGarbage.Proof.Poly1305.X86.Steps
import Mathlib.Tactic.Set

/-!
# Poly1305 on x86 (32-bit): absorbing a block

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

theorem carry_dec {x : Nat} (h : x < 2 ^ 33) : (decide (2 ^ 32 ≤ x)).toNat = x / 2 ^ 32 := by
  by_cases h' : 2 ^ 32 ≤ x
  · rw [decide_eq_true h', Bool.toNat_true]; omega
  · rw [decide_eq_false h', Bool.toNat_false]; omega

/-! ## `h += m + pad · 2¹²⁸` -/

section
variable (f : Nat → Nat) (b : Nat → Nat) (pad : Nat)
/-- The sums of the words of `h` and of the block, with the carries. -/
def asum : Nat → Nat
  | 0 => f 0 + b 0
  | k + 1 => f (k + 1) + (if k + 1 = 4 then pad else b (k + 1)) + asum k / 2 ^ 32
end

theorem addBlock_eq (b : Reg) (d : Nat) (pad : BitVec 32) : addBlock b d pad = addWord b d 0 ++
    (addWord b d 1 ++ (addWord b d 2 ++
    (addWord b d 3 ++ [.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm pad),
      .store (at_ .edi (hOff 4)) .eax]))) := by
  simp only [addBlock, List.append_assoc]

theorem asum_lt {f b : Nat → Nat} {pad : Nat} (hf : ∀ k < 5, f k < 2 ^ 32) (hb : ∀ k < 4, b k < 2 ^ 32)
    (hp : pad < 2 ^ 32) : ∀ k < 5, asum f b pad k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hf 0 (by omega); have := hb 0 (by omega); simp only [asum]; omega
  | succ k ih =>
    have := ih (by omega); have := hf (k + 1) hk
    simp only [asum]
    split
    · omega
    · have := hb (k + 1) (by omega); omega


theorem Words.congr {m : Mem} {st : BitVec 32} {g g' : Nat → Nat} (h : Words m st g)
    (he : ∀ k < 32, g k = g' k) : Words m st g' := fun k hk => (h k hk).trans (he k hk)

theorem After.congr {st : BitVec 32} {s s' : State} {g g' : Nat → Nat} {rs : List Reg}
    (h : After st s s' g rs) (he : ∀ k < 32, g k = g' k) : After st s s' g' rs :=
  ⟨h.words.congr he, h.frame, h.gpr, h.rd, h.wr⟩

section
variable (st bp : BitVec 32) (s : State) (f : Nat → Nat) (pad : BitVec 32)

/-- The block's words, as numbers. -/
abbrev bw (k : Nat) : Nat := wv s.mem bp (4 * k)

/-- After `addWord` for the words below `i`. -/
def AddInv (i : Nat) (s' : State) : Prop :=
  After st s s' (fun k => if k < i then asum f (bw bp s) pad.toNat k % 2 ^ 32 else f k) [.eax] ∧
    s'.cf = some (decide (2 ^ 32 ≤ asum f (bw bp s) pad.toNat (i - 1)))
end

/-- The hypotheses of `addBlock_ok`: the block at `b + d` is at `bp`, outside
the state or in its buffer (words 14 to 17). -/
structure AddPre (st bp : BitVec 32) (b : Reg) (d : Nat) (s : State) (f : Nat → Nat) : Prop where
  ctx : Ctx st s
  words : Words s.mem st f
  base : b ≠ .eax
  ea : ∀ k < 4, addr (s.gpr b) (d + 4 * k) = addr bp (4 * k)
  rd : ∀ k < 4, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4
  disj : ∀ k < 4, (sub bp (4 * k) 4).Disjoint (sR st) ∨ addr bp (4 * k) = addr st (4 * (14 + k))

theorem addFirst_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : AddPre st bp b d s f) (pad : BitVec 32) :
    WP isa (.block (addWord b d 0)) s (AddInv st bp s f pad 1) := by
  refine WP.mono (addWord_ok hp.ctx hp.words hp.base (i := 0) (by omega) (hp.ea 0 (by omega))
    (.inl ⟨rfl, rfl⟩) (hp.rd 0 (by omega))) fun s₁ ⟨A₁, c₁⟩ => ⟨A₁.congr fun k _ => ?_, by rw [c₁]; rfl⟩
  by_cases e : k = 0
  · subst e; simp [upd, asum, bw]
  · simp [upd, e]

theorem addStep_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : AddPre st bp b d s f) (pad : BitVec 32) {i : Nat} (hi : 1 ≤ i ∧ i < 4) {s' : State}
    (h : AddInv st bp s f pad i s') :
    WP isa (.block (addWord b d i)) s' (AddInv st bp s f pad (i + 1)) := by
  obtain ⟨A, c⟩ := h
  have hb : bw bp s' i = bw bp s i := by
    rcases hp.disj i (by omega) with hd | he
    · simp only [bw, wv]; rw [A.wd hd]
    · simp only [bw, wv, wd]
      rw [he, show (s'.mem.readW (addr st (4 * (14 + i))) 32).toNat = _ from A.words (14 + i) (by omega),
        show (s.mem.readW (addr st (4 * (14 + i))) 32).toNat = _ from hp.words (14 + i) (by omega),
        ite_eq_right (by omega)]
  have hlt := asum_lt (f := f) (b := bw bp s) (pad := pad.toNat) (fun k hk => hp.words.lt (by omega))
    (fun k _ => BitVec.isLt _) pad.isLt
  refine WP.mono (addWord_ok (bp := bp) (A.ctx hp.ctx) A.words hp.base (i := i) (by omega)
    (by rw [A.gpr _ (by simpa using hp.base)]; exact hp.ea i (by omega)) (.inr ⟨by omega, c⟩)
    (by rw [A.rd, A.wr]; exact hp.rd i (by omega)))
    fun s₁ ⟨A₁, c₁⟩ => ⟨(A.trans A₁).mono (rs' := [.eax]) |>.congr fun k _ => ?_, ?_⟩
  · rw [show bw bp s' i = wv s'.mem bp (4 * i) from rfl] at hb
    by_cases e : k = i
    · subst e
      simp only [upd, ite_true, show ¬ k < k by omega, ite_false, show k < k + 1 by omega]
      rw [hb, carry_dec (hlt (k - 1) (by omega))]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [asum, show j + 1 ≠ 4 by omega, ite_false, Nat.add_sub_cancel]
    · simp only [upd, e, ite_false]
      by_cases e' : k < i
      · simp [e', show k < i + 1 by omega]
      · simp [e', show ¬ k < i + 1 by omega]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega, show ¬ i < i by omega, ite_false]
    rw [show wv s'.mem bp (4 * i) = bw bp s i from hb, carry_dec (hlt (i - 1) (by omega))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [asum, show j + 1 ≠ 4 by omega, ite_false, Nat.add_sub_cancel]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`: the words `asum mod 2³²`. -/
theorem addBlock_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : AddPre st bp b d s f) (pad : BitVec 32) :
    WP isa (.block (addBlock b d pad)) s fun s' =>
      After st s s' (fun k => if k < 5 then asum f (bw bp s) pad.toNat k % 2 ^ 32 else f k) [.eax] := by
  have hlt := asum_lt (f := f) (b := bw bp s) (pad := pad.toNat) (fun k hk => hp.words.lt (by omega))
    (fun k _ => BitVec.isLt _) pad.isLt
  rw [addBlock_eq]
  refine WP.block_append (WP.mono (addFirst_ok hp pad) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (addStep_ok hp pad (i := 1) (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (addStep_ok hp pad (i := 2) (by omega) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (addStep_ok hp pad (i := 3) (by omega) h₃) fun s₄ ⟨A, c⟩ => ?_)
  refine WP.mono (los_ok (A.ctx hp.ctx) A.words (j := 4) (j' := 4) rfl rfl (by omega) (by omega)
    (.inr ⟨rfl, c⟩) (src_imm pad)) fun s₅ ⟨A₅, _⟩ => (A.trans A₅).mono (rs' := [.eax]) |>.congr fun k _ => ?_
  by_cases e : k = 4
  · subst e
    simp only [upd, ite_true, show ¬ (4 : Nat) < 4 by omega, ite_false, show (4 : Nat) < 5 by omega]
    rw [carry_dec (hlt 3 (by omega))]
    simp only [asum, ite_true, show (3 : Nat) + 1 = 4 from rfl]
  · simp only [upd, e, ite_false]
    by_cases e' : k < 4
    · simp [e', show k < 5 by omega]
    · simp [e', show ¬ k < 5 by omega]


/-! ## The sums of products -/

/-- The word index of the coefficient of `hi` in `dk` (`coef k i = 4 * cidx k i`). -/
def cidx (k i : Nat) : Nat := if i ≤ k then 18 + (k - i) else 21 + (k + 4 - i)

theorem coef_eq (k i : Nat) : coef k i = 4 * cidx k i := by
  simp only [coef, cidx, rOff, sOff]; split <;> omega

theorem cidx_lt : ∀ k < 4, ∀ i < 5, cidx k i < 32 ∧ 18 ≤ cidx k i ∧ cidx k i < 25 := by decide

section
variable (g : Nat → Nat)
/-- `dk`'s sum of products, from the words `g`. -/
def dterm (k : Nat) : Nat := ((List.range (nterms k)).map fun i => g i * g (cidx k i)).sum

/-- `dk`, with the carries from `d(k-1)`. -/
def dv : Nat → Nat
  | 0 => dterm g 0
  | k + 1 => dv k / 2 ^ 32 + dterm g (k + 1)
end

theorem dsum_eq (k : Nat) : dsum k = (((List.range (nterms k)).map fun i => (i, coef k i)).flatMap
    fun p => mac p.1 p.2) ++ [.store (at_ .edi (tOff k)) .ebx, .mov .ebx (.reg .ebp), .mov .ebp (.imm 0)] := by
  rw [dsum, List.flatMap_map]

/-- `dk`, from the accumulator `A` in `ebx:ebp`: its low word stored, and its
high word as the new accumulator. -/
theorem dsum_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {g : Nat → Nat} (hw : Words s.mem st g)
    {k : Nat} (hk : k < 4) (hb : acc s + dterm g k < 2 ^ 64) :
    WP isa (.block (dsum k)) s fun s' =>
      After st s s' (upd g (25 + k) ((acc s + dterm g k) % 2 ^ 32)) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      acc s' = (acc s + dterm g k) / 2 ^ 32 := by
  have hfit := hc.fit
  rw [dsum_eq]
  have hL : ∀ p ∈ ((List.range (nterms k)).map fun i => (i, coef k i)),
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff p.1)) 4 ∧
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) p.2) 4 := by
    intro p hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega
    obtain ⟨-, -, h3⟩ := cidx_lt k hk i (by omega)
    exact ⟨hc.inRW' (by simp only [hOff]; omega), hc.inRW' (by rw [coef_eq]; omega)⟩
  have hsum : (((List.range (nterms k)).map fun i => (i, coef k i)).map fun p =>
      wv s.mem (s.gpr .edi) (hOff p.1) * wv s.mem (s.gpr .edi) p.2).sum = dterm g k := by
    rw [List.map_map, dterm]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega
    obtain ⟨h1, -, -⟩ := cidx_lt k hk i (by omega)
    simp only [Function.comp_apply, hc.edi, hOff, coef_eq]
    rw [hw i (by omega), hw _ h1]
  refine WP.block_append (WP.mono (macs_ok _ s hL) fun s₁ ⟨e₁, k₁⟩ => ?_)
  rw [hsum] at e₁
  have e₁ := e₁ hb
  have edi₁ : s₁.gpr .edi = st := by rw [k₁.gpr', hc.edi]
  have hebp : v s₁ .ebp = (acc s + dterm g k) / 2 ^ 32 := by
    have := (s₁.gpr .ebx).isLt; simp only [acc, v] at e₁ ⊢; omega
  have hebx : v s₁ .ebx = (acc s + dterm g k) % 2 ^ 32 := by
    have := (s₁.gpr .ebx).isLt; simp only [acc, v] at e₁ ⊢; omega
  refine wp_store (a := addr st (tOff k)) (by rw [ea_at, edi₁])
    (by rw [k₁.2.2.2]; exact hc.inW (by simp only [tOff]; omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ _ => wp_movi fun s₄ u₄ _ => WP.block_nil ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, k₁.2.1, show tOff k = 4 * (25 + k) by simp only [tOff]; omega]
    rw [← hebx]
    exact hw.write hfit (by omega) _
  · rw [u₄.mem, u₃.mem, u₂.mem, k₁.2.1]
    exact frame_write (Frame.refl _ _) hfit (by simp only [tOff]; omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other r hr.2.2.2.2, u₃.other r hr.2.2.2.1, u₂.gpr, k₁.1 r (by simp [hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [u₄.rd, u₃.rd, u₂.rd, k₁.2.2.1]
  · rw [u₄.wr, u₃.wr, u₂.wr, k₁.2.2.2]
  · simp only [acc, v]
    rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    have : (0 : BitVec 32).toNat = 0 := rfl
    rw [this, ← hebp]
    simp only [v]; omega


theorem dterm_congr {g g' : Nat → Nat} (h : ∀ i < 25, g i = g' i) {k : Nat} (hk : k < 4) :
    dterm g k = dterm g' k := by
  simp only [dterm]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega
  obtain ⟨-, -, h3⟩ := cidx_lt k hk i (by omega)
  rw [h i (by omega), h _ h3]

/-- The words after `n` of the sums of products: `tk = dk mod 2³²`. -/
def dwords (g : Nat → Nat) (n : Nat) : Nat → Nat :=
  fun k => if 25 ≤ k ∧ k < 25 + n then dv g (k - 25) % 2 ^ 32 else g k

theorem dsums_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {g : Nat → Nat} (hw : Words s.mem st g)
    (hacc : acc s = 0) (hb : ∀ k < 4, dv g k < 2 ^ 64) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap dsum)) s fun s' =>
      After st s s' (dwords g n) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      acc s' = if n = 0 then 0 else dv g (n - 1) / 2 ^ 32 := by
  intro n hn
  induction n with
  | zero =>
    refine WP.block_nil ⟨⟨hw.congr fun k _ => ?_, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩, hacc⟩
    simp [dwords]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨A₁, e₁⟩ => ?_)
    have hd : dterm (dwords g n) n = dterm g n :=
      dterm_congr (fun i hi => by simp only [dwords]; rw [ite_eq_right (by omega)]) (by omega)
    have hv : acc s₁ + dterm (dwords g n) n = dv g n := by
      rw [hd, e₁]
      cases n with
      | zero => simp [dv]
      | succ n => simp [dv]
    refine WP.mono (dsum_ok (A₁.ctx hc) A₁.words (k := n) (by omega) (by rw [hv]; exact hb n (by omega)))
      fun s₂ ⟨A₂, e₂⟩ => ⟨(A₁.trans A₂).mono.congr fun k _ => ?_, by rw [e₂, hv]; simp⟩
    rw [hv]
    simp only [upd, dwords]
    by_cases e : k = 25 + n
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases e' : 25 ≤ k ∧ k < 25 + n
      · rw [ite_eq_left e', ite_eq_left ⟨e'.1, by omega⟩]
      · rw [ite_eq_right e', ite_eq_right (by omega)]

theorem products_eq : products = .mov .ebx (.imm 0) :: .mov .ebp (.imm 0) ::
    ((List.range 4).flatMap dsum ++ mac 4 (rOff 0)) := by
  simp only [products, List.cons_append, List.nil_append]

/-- The sums of products: `t0, …, t3` stored, and `d4` in `ebx`. -/
theorem products_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {g : Nat → Nat} (hw : Words s.mem st g)
    (hb : ∀ k < 4, dv g k < 2 ^ 64) (h4 : dv g 3 / 2 ^ 32 + g 4 * g 18 < 2 ^ 32) :
    WP isa (.block products) s fun s' =>
      After st s s' (dwords g 4) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      v s' .ebx = dv g 3 / 2 ^ 32 + g 4 * g 18 := by
  rw [products_eq]
  refine wp_movi fun s₁ u₁ _ => wp_movi fun s₂ u₂ _ => ?_
  have A₂ : After st s s₂ g [.eax, .ecx, .edx, .ebx, .ebp] :=
    ⟨by rw [u₂.mem, u₁.mem]; exact hw, by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other r hr.2.2.2.2, u₁.other r hr.2.2.2.1], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have hacc : acc s₂ = 0 := by
    simp only [acc, v]; rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  refine WP.block_append (WP.mono (dsums_ok (A₂.ctx hc) A₂.words hacc hb 4 (Nat.le_refl _))
    fun s₃ ⟨A₃, e₃⟩ => ?_)
  have c₃ := (A₂.trans A₃).ctx hc
  refine WP.mono (mac_ok s₃ 4 (rOff 0) (c₃.inRW' (by simp [hOff])) (c₃.inRW' (by simp [rOff])))
    fun s₄ ⟨e₄, k₄⟩ => ⟨?_, ?_⟩
  · exact ⟨k₄.2.1 ▸ A₃.words, A₂.frame.trans (k₄.2.1 ▸ A₃.frame), fun r hr => by
      rw [k₄.1 r hr, A₃.gpr r hr, A₂.gpr r hr], by rw [k₄.2.2.1, A₃.rd, A₂.rd],
      by rw [k₄.2.2.2, A₃.wr, A₂.wr]⟩
  · have w4 : wv s₃.mem (s₃.gpr .edi) (hOff 4) = g 4 := by
      rw [c₃.edi, show hOff 4 = 4 * 4 from rfl, A₃.words 4 (by omega)]; simp [dwords]
    have w14 : wv s₃.mem (s₃.gpr .edi) (rOff 0) = g 18 := by
      rw [c₃.edi, show rOff 0 = 4 * 18 from rfl, A₃.words 18 (by omega)]; simp [dwords]
    rw [w4, w14, show acc s₃ = dv g 3 / 2 ^ 32 by rw [e₃]; rfl] at e₄
    have e₄ := e₄ (by omega)
    simp only [acc, v] at e₄ ⊢
    omega


/-! ## The carry -/

section
variable (G : Nat → Nat) (d4 : Nat)
/-- The sums of `5 ⌊d4 / 4⌋ + t` and `2¹²⁸ (d4 mod 4)`, with the carries. -/
def csum : Nat → Nat
  | 0 => 5 * (d4 / 4) + G 25
  | k + 1 => (if k + 1 = 4 then d4 % 4 else G (25 + (k + 1))) + csum k / 2 ^ 32
end

theorem csum_lt {G : Nat → Nat} {d4 : Nat} (hG : ∀ k < 4, G (25 + k) < 2 ^ 32)
    (he : 5 * (d4 / 4) < 2 ^ 32) : ∀ k < 5, csum G d4 k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hG 0 (by omega); simp only [Nat.add_zero] at this; simp only [csum]; omega
  | succ k ih =>
    have := ih (by omega)
    simp only [csum]
    split
    · omega
    · have := hG (k + 1) (by omega); omega

theorem carry_eq : carry =
    [.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .alu .and .ebx (.imm 3),
      .alu .add .eax (.mem (at_ .edi (tOff 0))), .store (at_ .edi (hOff 0)) .eax] ++
    ([.mov .eax (.mem (at_ .edi (tOff 1))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 1)) .eax] ++
    ([.mov .eax (.mem (at_ .edi (tOff 2))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 2)) .eax] ++
    ([.mov .eax (.mem (at_ .edi (tOff 3))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 3)) .eax] ++
    [.alu .adc .ebx (.imm 0), .store (at_ .edi (hOff 4)) .ebx]))) := rfl

section
variable (st : BitVec 32) (s : State) (G : Nat → Nat) (d4 : Nat)
/-- After the carry into the words below `i`. -/
def CInv (i : Nat) (s' : State) : Prop :=
  After st s s' (fun k => if k < i then csum G d4 k % 2 ^ 32 else G k) [.eax, .ecx, .ebx] ∧
    s'.cf = some (decide (2 ^ 32 ≤ csum G d4 (i - 1))) ∧ v s' .ebx = d4 % 4
end

theorem shr2_toNat (x : BitVec 32) : (x >>> 2).toNat = x.toNat / 4 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and3_toNat (x : BitVec 32) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

/-- `5 ⌊d4 / 4⌋ + t0`, with `d4 mod 4` left in `ebx`. -/
theorem carryHead_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {G : Nat → Nat}
    (hw : Words s.mem st G) {d4 : Nat} (hd4 : v s .ebx = d4) (he : 5 * (d4 / 4) < 2 ^ 32) :
    WP isa (.block [.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
      .alu .and .ebx (.imm 3), .alu .add .eax (.mem (at_ .edi (tOff 0))),
      .store (at_ .edi (hOff 0)) .eax]) s (CInv st s G d4 1) := by
  have hfit := hc.fit
  refine wp_mov fun s₁ u₁ _ => wp_shr (by omega) fun s₂ u₂ => wp_mov fun s₃ u₃ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₄ u₄ _ => wp_addx (readSrc_reg _ _) fun s₅ u₅ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₆ u₆ _ => wp_andx (readSrc_imm _ _) fun s₇ u₇ => ?_
  have edi₇ : s₇.gpr .edi = st := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  have mem₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- `eax = 5 ⌊d4 / 4⌋`.
  have q : (s₂.gpr .eax).toNat = d4 / 4 := by rw [u₂.gpr, u₁.gpr, shr2_toNat, ← hd4]
  have hq : d4 / 4 < 2 ^ 30 := by have := (s.gpr .ebx).isLt; simp only [v] at hd4; omega
  have e₇ : (s₇.gpr .eax).toNat = 5 * (d4 / 4) := by
    rw [u₇.other .eax (by decide), u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.gpr,
      u₄.other .ecx (by decide), u₃.gpr, u₃.other .eax (by decide)]
    simp only [BitVec.toNat_add, q]
    omega
  have b₇ : v s₇ .ebx = d4 % 4 := by
    simp only [v]
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), and3_toNat]
    rw [← hd4]
  refine wp_addx (readSrc_mem (a := addr st (tOff 0)) (by rw [ea_at, edi₇])
    (by rw [rd₇, wr₇]; exact hc.inRW (by simp [tOff]) (by omega))) fun s₈ u₈ c₈ => ?_
  have t0 : (s₇.mem.readW (addr st (tOff 0)) 32).toNat = G 25 := by rw [mem₇]; exact hw 25 (by omega)
  refine wp_store (a := addr st (4 * 0)) (by rw [ea_at, u₈.other _ (by decide), edi₇]; rfl)
    (by rw [u₈.wr, wr₇]; exact hc.inW (by omega) (by omega)) fun s₉ u₉ => WP.block_nil ⟨⟨?_, ?_,
      fun r hr => ?_, by rw [u₉.rd, u₈.rd, rd₇], by rw [u₉.wr, u₈.wr, wr₇]⟩, ?_, ?_⟩
  · rw [u₉.mem, u₈.mem, mem₇]
    refine (hw.write hfit (by omega) _).congr fun k _ => ?_
    by_cases e : k = 0
    · subst e
      simp only [upd, ite_true, show (0 : Nat) < 1 by omega, csum]
      rw [u₈.gpr, BitVec.toNat_add, e₇, t0]
    · simp only [upd, e, ite_false, show ¬ k < 1 by omega]
  · rw [u₉.mem, u₈.mem, mem₇]; exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₉.gpr, u₈.other r hr.1, u₇.other r hr.2.2, u₆.other r hr.1, u₅.other r hr.1,
      u₄.other r hr.1, u₃.other r hr.2.1, u₂.other r hr.1, u₁.other r hr.1]
  · rw [u₉.cf, c₈, e₇, t0]; rfl
  · simp only [v]; rw [u₉.gpr, u₈.other _ (by decide)]; exact b₇

/-- The carry into word `i` (`1 ≤ i ≤ 3`). -/
theorem carryStep_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {G : Nat → Nat}
    (hw : Words s.mem st G) {d4 : Nat} (he : 5 * (d4 / 4) < 2 ^ 32) {i : Nat} (hi : 1 ≤ i ∧ i < 4)
    {s' : State} (h : CInv st s G d4 i s') :
    WP isa (.block [.mov .eax (.mem (at_ .edi (tOff i))), .alu .adc .eax (.imm 0),
      .store (at_ .edi (hOff i)) .eax]) s' (CInv st s G d4 (i + 1)) := by
  obtain ⟨A, c, b⟩ := h
  have hlt := csum_lt (G := G) (d4 := d4) (fun k hk => hw.lt (by omega)) he
  refine WP.mono (los_ok (A.ctx hc) A.words (j := 25 + i) (j' := i) (by simp only [tOff]; omega) rfl
    (by omega) (by omega) (.inr ⟨rfl, c⟩) (src_imm 0)) fun s₁ ⟨A₁, c₁⟩ =>
      ⟨(A.trans A₁).mono.congr fun k _ => ?_, ?_, ?_⟩
  · simp only [upd]
    by_cases e : k = i
    · subst e
      simp only [ite_true, show ¬ 25 + k < k by omega, ite_false, show k < k + 1 by omega]
      rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, carry_dec (hlt (k - 1) (by omega))]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [csum, show j + 1 ≠ 4 by omega, ite_false, Nat.add_sub_cancel]
    · rw [ite_eq_right e]
      by_cases e' : k < i
      · simp [e', show k < i + 1 by omega]
      · simp [e', show ¬ k < i + 1 by omega]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega, show ¬ 25 + i < i by omega, ite_false]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, carry_dec (hlt (i - 1) (by omega))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [csum, show j + 1 ≠ 4 by omega, ite_false, Nat.add_sub_cancel]
  · simp only [v]; rw [A₁.gpr _ (by decide)]; exact b

/-- The carries of `absorb`: the words `csum mod 2³²`. -/
theorem carry_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {G : Nat → Nat}
    (hw : Words s.mem st G) {d4 : Nat} (hd4 : v s .ebx = d4) (he : 5 * (d4 / 4) < 2 ^ 32) :
    WP isa (.block carry) s fun s' =>
      After st s s' (fun k => if k < 5 then csum G d4 k % 2 ^ 32 else G k) [.eax, .ecx, .ebx] := by
  have hfit := hc.fit
  have hlt := csum_lt (G := G) (d4 := d4) (fun k hk => hw.lt (by omega)) he
  rw [carry_eq]
  refine WP.block_append (WP.mono (carryHead_ok hc hw hd4 he) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (carryStep_ok hc hw he (i := 1) (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (carryStep_ok hc hw he (i := 2) (by omega) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (carryStep_ok hc hw he (i := 3) (by omega) h₃)
    fun s₄ ⟨A, c, b⟩ => ?_)
  have c₄ := A.ctx hc
  refine wp_adcx (readSrc_imm _ _) c fun s₅ u₅ c₅ => ?_
  refine wp_store (a := addr st (4 * 4)) (by rw [ea_at, u₅.other _ (by decide), c₄.edi]; rfl)
    (by rw [u₅.wr]; exact c₄.inW (by omega) (by omega)) fun s₆ u₆ => WP.block_nil ?_
  have A₆ : After st s₄ s₆ (upd (fun k => if k < 4 then csum G d4 k % 2 ^ 32 else G k) 4
      (s₅.gpr .ebx).toNat) [.ebx] := by
    refine ⟨?_, ?_, fun r hr => ?_, by rw [u₆.rd, u₅.rd], by rw [u₆.wr, u₅.wr]⟩
    · rw [u₆.mem, u₅.mem]; exact A.words.write hfit (j := 4) (by omega) _
    · rw [u₆.mem, u₅.mem]; exact frame_write (Frame.refl _ _) hfit (d := 4 * 4) (by omega) _
    · simp only [List.mem_singleton] at hr; rw [u₆.gpr, u₅.other r hr]
  refine (A.trans A₆).mono.congr fun k _ => ?_
  · simp only [upd]
    by_cases e : k = 4
    · subst e
      simp only [ite_true, show (4 : Nat) < 5 by omega]
      rw [u₅.gpr, add3_toNat, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero,
        carry_dec (hlt 3 (by omega))]
      simp only [v] at b
      rw [b]
      simp only [csum, ite_true, show (3 : Nat) + 1 = 4 from rfl]
    · rw [ite_eq_right e]
      by_cases e' : k < 4
      · simp [e', show k < 5 by omega]
      · simp [e', show ¬ k < 5 by omega]


/-! ## Absorbing a block -/

/-- The clamped `r` in the state's words: `r0`, `rj = 4 qj` and `sj = 5 qj`. -/
structure Coefs (f : Nat → Nat) (r0 q1 q2 q3 : Nat) : Prop where
  r0e : f 18 = r0
  r1e : f 19 = 4 * q1
  r2e : f 20 = 4 * q2
  r3e : f 21 = 4 * q3
  s1e : f 22 = 5 * q1
  s2e : f 23 = 5 * q2
  s3e : f 24 = 5 * q3
  r0_lt : r0 < 2 ^ 28
  q1_lt : q1 < 2 ^ 26
  q2_lt : q2 < 2 ^ 26
  q3_lt : q3 < 2 ^ 26

theorem Coefs.congr {f g : Nat → Nat} {r0 q1 q2 q3 : Nat} (h : Coefs f r0 q1 q2 q3)
    (he : ∀ k, 18 ≤ k → k < 25 → g k = f k) : Coefs g r0 q1 q2 q3 :=
  ⟨(he 18 (by omega) (by omega)).trans h.r0e, (he 19 (by omega) (by omega)).trans h.r1e,
    (he 20 (by omega) (by omega)).trans h.r2e, (he 21 (by omega) (by omega)).trans h.r3e,
    (he 22 (by omega) (by omega)).trans h.s1e, (he 23 (by omega) (by omega)).trans h.s2e,
    (he 24 (by omega) (by omega)).trans h.s3e, h.r0_lt, h.q1_lt, h.q2_lt, h.q3_lt⟩

section
variable (g : Nat → Nat)
theorem dterm0 : dterm g 0 = g 0 * g 18 + (g 1 * g 24 + (g 2 * g 23 + (g 3 * g 22 + 0))) := rfl
theorem dterm1 : dterm g 1 =
    g 0 * g 19 + (g 1 * g 18 + (g 2 * g 24 + (g 3 * g 23 + (g 4 * g 22 + 0)))) := rfl
theorem dterm2 : dterm g 2 =
    g 0 * g 20 + (g 1 * g 19 + (g 2 * g 18 + (g 3 * g 24 + (g 4 * g 23 + 0)))) := rfl
theorem dterm3 : dterm g 3 =
    g 0 * g 21 + (g 1 * g 20 + (g 2 * g 19 + (g 3 * g 18 + (g 4 * g 24 + 0)))) := rfl
end

/-- `h` in the state's words. -/
abbrev hw5 (f : Nat → Nat) : Nat := val5 (f 0) (f 1) (f 2) (f 3) (f 4)

theorem absorbAt_eq (b : Reg) (d : Nat) (pad : BitVec 32) :
    absorbAt b d pad = addBlock b d pad ++ (products ++ carry) := by
  simp only [absorbAt, List.append_assoc]

/-- Absorbing the block at `b + d`: from `h` with `h4 ≤ 4`, the new `h` is
congruent to `(h + m + pad · 2¹²⁸) r` modulo `p`, and its `h4` is at most 4. -/
theorem absorb_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : AddPre st bp b d s f)
    {r0 q1 q2 q3 : Nat} (hco : Coefs f r0 q1 q2 q3) (hh4 : f 4 ≤ 4) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) :
    WP isa (.block (absorbAt b d pad)) s fun s' => ∃ g, After st s s' g [.eax, .ecx, .edx, .ebx, .ebp] ∧
      (∀ k, 5 ≤ k → k < 25 → g k = f k) ∧ (∀ k, 29 ≤ k → g k = f k) ∧
      hw5 g % P = ((hw5 f + (bw bp s 0 + 2 ^ 32 * bw bp s 1 + 2 ^ 64 * bw bp s 2 + 2 ^ 96 * bw bp s 3 +
        2 ^ 128 * pad.toNat)) * rval r0 q1 q2 q3) % P ∧ g 4 ≤ 4 := by
  have hc := hp.ctx
  have hf : ∀ k < 32, f k < 2 ^ 32 := fun k hk => hp.words.lt hk
  rw [absorbAt_eq]
  refine WP.block_append (WP.mono (addBlock_ok hp pad) fun s₁ A₁ => ?_)
  -- The words of `h + m`.
  set a : Nat → Nat := fun k => if k < 5 then asum f (bw bp s) pad.toNat k % 2 ^ 32 else f k with ha
  have hlt := asum_lt (f := f) (b := bw bp s) (pad := pad.toNat) (fun k hk => hf k (by omega))
    (fun k _ => BitVec.isLt _) pad.isLt
  obtain ⟨hsum, ha4⟩ := add_arith (h0 := f 0) (h1 := f 1) (h2 := f 2) (h3 := f 3) (h4 := f 4)
    (m0 := bw bp s 0) (m1 := bw bp s 1) (m2 := bw bp s 2) (m3 := bw bp s 3) (pad := pad.toNat)
    (u0 := a 0) (u1 := a 1) (u2 := a 2) (u3 := a 3) (u4 := a 4) (hf 0 (by omega)) (hf 1 (by omega))
    (hf 2 (by omega)) (hf 3 (by omega)) hh4 (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) hpad (by simp [ha, asum]) (by simp [ha, asum]) (by simp [ha, asum])
    (by simp [ha, asum]) (by simp [ha, asum])
  have hco₁ : Coefs a r0 q1 q2 q3 := hco.congr fun k h₁ _ => by simp only [ha]; rw [ite_eq_right (by omega)]
  -- The sums of products.
  have ha' : ∀ k < 4, a k < 2 ^ 32 := fun k hk => by
    simp only [ha]; rw [ite_eq_left (by omega)]; exact Nat.mod_lt _ (by omega)
  obtain ⟨b0, b1, b2, b3, b4, b5, hW⟩ := absorb_arith (a0 := a 0) (a1 := a 1) (a2 := a 2) (a3 := a 3)
    (a4 := a 4) (r0 := r0) (q1 := q1) (q2 := q2) (q3 := q3) (d0 := dv a 0) (d1 := dv a 1) (d2 := dv a 2)
    (d3 := dv a 3) (d4 := dv a 3 / 2 ^ 32 + a 4 * a 18) (ha' 0 (by omega)) (ha' 1 (by omega))
    (ha' 2 (by omega)) (ha' 3 (by omega)) ha4 hco.r0_lt hco.q1_lt hco.q2_lt hco.q3_lt
    (by rw [show dv a 0 = dterm a 0 from rfl, dterm0, hco₁.r0e, hco₁.s1e, hco₁.s2e, hco₁.s3e, Nat.zero_add])
    (by rw [show dv a 1 = dv a 0 / 2 ^ 32 + dterm a 1 from rfl, dterm1, hco₁.r0e, hco₁.r1e, hco₁.s1e, hco₁.s2e, hco₁.s3e])
    (by rw [show dv a 2 = dv a 1 / 2 ^ 32 + dterm a 2 from rfl, dterm2, hco₁.r0e, hco₁.r1e, hco₁.r2e, hco₁.s2e, hco₁.s3e])
    (by rw [show dv a 3 = dv a 2 / 2 ^ 32 + dterm a 3 from rfl, dterm3, hco₁.r0e, hco₁.r1e, hco₁.r2e, hco₁.r3e, hco₁.s3e])
    (by simp only [hco₁.r0e])
  have hb : ∀ k < 4, dv a k < 2 ^ 64 := fun k hk => by
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    exacts [b0, b1, b2, b3]
  refine WP.block_append (WP.mono (products_ok (A₁.ctx hc) A₁.words hb b4) fun s₂ ⟨A₂, e₂⟩ => ?_)
  -- The carries.
  refine WP.mono (carry_ok ((A₁.trans A₂).ctx hc) A₂.words e₂ b5) fun s₃ A₃ => ?_
  set d4 := dv a 3 / 2 ^ 32 + a 4 * a 18
  have hG : ∀ k < 4, dwords a 4 (25 + k) = dv a k % 2 ^ 32 := fun k hk => by
    simp only [dwords]; rw [ite_eq_left (by omega)]; congr 2; omega
  obtain ⟨hu, hu4⟩ := carry_arith (t0 := dv a 0 % 2 ^ 32) (t1 := dv a 1 % 2 ^ 32) (t2 := dv a 2 % 2 ^ 32)
    (t3 := dv a 3 % 2 ^ 32) (d4 := d4) (e := 5 * (d4 / 4))
    (u0 := csum (dwords a 4) d4 0 % 2 ^ 32) (u1 := csum (dwords a 4) d4 1 % 2 ^ 32)
    (u2 := csum (dwords a 4) d4 2 % 2 ^ 32) (u3 := csum (dwords a 4) d4 3 % 2 ^ 32)
    (u4 := csum (dwords a 4) d4 4 % 2 ^ 32) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) b5
    (by simp only [csum]; rw [← hG 0 (by omega)])
    (by simp only [csum]; rw [← hG 0 (by omega), ← hG 1 (by omega)]; rfl)
    (by simp only [csum]; rw [← hG 0 (by omega), ← hG 1 (by omega), ← hG 2 (by omega)]; rfl)
    (by simp only [csum]; rw [← hG 0 (by omega), ← hG 1 (by omega), ← hG 2 (by omega),
      ← hG 3 (by omega)]; rfl)
    (by simp only [csum]; rw [← hG 0 (by omega), ← hG 1 (by omega), ← hG 2 (by omega),
      ← hG 3 (by omega)]; rfl)
  refine ⟨_, ((A₁.trans A₂).trans A₃).mono, fun k h₁ h₂ => ?_, fun k h₁ => ?_, ?_, ?_⟩
  · simp only [dwords, ha]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [dwords, ha]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [hw5, show (0 : Nat) < 5 by omega, show (1 : Nat) < 5 by omega, show (2 : Nat) < 5 by omega,
      show (3 : Nat) < 5 by omega, show (4 : Nat) < 5 by omega, ite_true]
    rw [hu, hW, hsum]
  · simp only [show (4 : Nat) < 5 by omega, ite_true]; exact hu4

end VG.Proof.Poly1305.X86
