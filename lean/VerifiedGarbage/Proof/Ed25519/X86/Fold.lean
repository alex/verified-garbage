import VerifiedGarbage.Proof.Ed25519.X86.Column
import VerifiedGarbage.Proof.X25519.Field

/-!
# Ed25519 on x86 (32-bit): folding a carry, and linear combinations

Untrusted: everything here is checked by Lean. `fold` adds `38 c` for the
carry `c` in the accumulator (as `2²⁵⁶ ≡ 38` modulo `p`), which leaves a
carry of at most 1, added as 38 more to the lowest word, which cannot carry
again. `linear_ok`: an element summed by eight columns and folded is their
sum modulo `p`.
-/

namespace VG.Proof.Ed25519.X86

open VG.Proof.X25519
open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- `mul r`: `edx:eax = eax · r`, the other registers, memory and regions kept. -/
structure MulUpd (s s' : State) (r : Reg) : Prop where
  eax : v s' .eax = (v s .eax * v s r) % 2 ^ 32
  edx : v s' .edx = (v s .eax * v s r) / 2 ^ 32
  other : ∀ q, q ≠ .eax → q ≠ .edx → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : ∀ s', MulUpd s s' r → WP isa (.block is) s' Q) : WP isa (.block (.mul r :: is)) s Q := by
  refine Wp.cons (s' := execMul r s) rfl (k _ ⟨?_, ?_, fun q h₁ h₂ => ?_, rfl, rfl, rfl⟩)
  · simp (config := {decide := true}) only [execMul, v, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      ite_false, ite_true, BitVec.toNat_ofNat]
  · simp only [execMul, v, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, BitVec.toNat_ofNat, ite_true]
    have := Nat.mul_lt_mul_of_lt_of_lt (s.gpr .eax).isLt (s.gpr r).isLt
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])
  · simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, h₁, h₂, ite_false]

theorem MulUpd.keep {s s' : State} {r : Reg} (h : MulUpd s s' r) : Keep s s' :=
  ⟨h.other _ (by decide) (by decide), h.other _ (by decide) (by decide), h.other _ (by decide) (by decide),
    h.rd, h.wr⟩

/-- The accumulator's three words, when it is less than `2³²`. -/
theorem acc_small {s : State} {c : Nat} (h : acc s = c) (hc : c < 2 ^ 32) :
    v s .ebx = c ∧ v s .ecx = 0 ∧ v s .ebp = 0 := by
  simp only [acc] at h
  omega_using [h, hc]

/-- `num` with its lowest digit increased by `d`. -/
theorem num_add0 {f g : Nat → Nat} {n d : Nat} (hn : 1 ≤ n) (h0 : g 0 = f 0 + d)
    (h : ∀ k, 1 ≤ k → k < n → g k = f k) : num g n = num f n + d := by
  induction n with
  | zero => omega_using [hn]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [num, Nat.pow_zero, Nat.one_mul, Nat.zero_add, h0]
    · rw [num_succ, num_succ, ih hpos fun k h₁ h₂ => h k h₁ (by omega_using [h₂]),
        h n hpos (by omega_using [])]
      omega_using []

theorem le_num {f : Nat → Nat} {n : Nat} (hn : 1 ≤ n) : f 0 ≤ num f n := by
  induction n with
  | zero => omega_using [hn]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [num, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.le_refl]
    · rw [num_succ]; have := ih hpos; omega_using [this]

theorem toNat_38 : (38 : BitVec 32).toNat = 38 := rfl

theorem head_ok {s : State} {c : Nat} (hc : acc s = c) (hc' : c < 2 ^ 26) :
    WP isa (.block [.mov .eax (.imm 38), .mul .ebx, .mov .ebx (.reg .eax)]) s fun s' =>
      Keep s s' ∧ s'.mem = s.mem ∧ acc s' = 38 * c := by
  obtain ⟨hb, hcx, hbp⟩ := acc_small hc (by omega_using [hc'])
  refine Wp.wp_movi fun s₁ u₁ => wp_mul fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(updKeep u₁).trans (u₂.keep.trans (updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  have e₂ : v s₂ .eax = 38 * c := by
    rw [u₂.eax, v, u₁.gpr, v, u₁.other _ (by decide), ← v, hb, toNat_38]
    exact Nat.mod_eq_of_lt (by omega_using [hc'])
  simp only [acc, v, u₃.gpr, u₃.other .ecx (by decide), u₃.other .ebp (by decide),
    u₂.other .ecx (by decide) (by decide), u₂.other .ebp (by decide) (by decide),
    u₁.other .ecx (by decide), u₁.other .ebp (by decide)]
  simp only [v] at e₂ hcx hbp
  rw [e₂, hcx, hbp]; omega_using []

theorem tail_ok {x : BitVec 32} {s : State} (hctx : Ctx x s) {o c : Nat} (ho : o + 4 ≤ 8192)
    (hc : acc s = c) (hc' : c ≤ 1) (hw : wv s.mem x o + 38 * c < 2 ^ 32) :
    WP isa (.block [.mov .eax (.imm 38), .mul .ebx, .alu .add .eax (.mem (sc o)), .store (sc o) .eax]) s
      fun s' => Keep s s' ∧ Frame [sub x o 4] s.mem s'.mem ∧ wv s'.mem x o = wv s.mem x o + 38 * c := by
  obtain ⟨hb, -, -⟩ := acc_small hc (by omega_using [hc'])
  refine Wp.wp_movi fun s₁ u₁ => wp_mul fun s₂ u₂ => ?_
  have c₂ := u₂.keep.ctx ((updKeep u₁).ctx hctx)
  refine Wp.wp_addm c₂.edi (c₂.inRW ho (by decide)) fun s₃ u₃ => ?_
  have c₃ := (updKeep u₃).ctx c₂
  refine Wp.wp_stm c₃.edi (c₃.inW ho (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨(updKeep u₁).trans (u₂.keep.trans ((updKeep u₃).trans ⟨by rw [u₄.gpr], by rw [u₄.gpr],
    by rw [u₄.gpr], u₄.rd, u₄.wr⟩)), ?_, ?_⟩
  · rw [u₄.mem, u₃.mem, m₂]
    exact frame_write1 (Frame.refl _ _) hctx.fit ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [u₄.mem, u₃.mem, u₃.gpr, m₂, wv, wd_write_self, BitVec.toNat_add]
    have e₂ : v s₂ .eax = 38 * c := by
      rw [u₂.eax, v, u₁.gpr, v, u₁.other _ (by decide), ← v, hb, toNat_38]
      exact Nat.mod_eq_of_lt (by omega_using [hc'])
    simp only [v] at e₂
    rw [e₂]
    simp only [wv, wd] at hw ⊢
    omega_using [hw]

/-- The fold of the carry `c < 2²⁶` in the accumulator into the element at
`[x + o]`. -/
theorem fold_ok {x : BitVec 32} {s : State} (hctx : Ctx x s) {o c : Nat} (ho : o + 32 ≤ 8192)
    (hc : acc s = c) (hc' : c < 2 ^ 26) :
    WP isa (.block (fold o)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = (fe s.mem x o + 38 * c) % P := by
  have hfit := hctx.fit
  refine WP.block_append (WP.block_append (WP.mono (head_ok hc hc') fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))
  have c₁ := k₁.ctx hctx
  refine WP.mono (cols_ok c₁ (fun k => [.addM (o + 4 * k)]) 8 ho (fun k hk t ht d hd => ?_)
    (fun k hk => ?_) (by rw [a₁]; omega_using [hc'])) fun s₂ ⟨k₂, f₂, e₂, a₂⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [ho, hk], .inr (Nat.le_refl _)⟩
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := BitVec.isLt (wd s₁.mem x (o + 4 * k)); simp only [wv, wd] at this ⊢; omega_using [this]
  · -- The columns' sum is the element plus `38 c`, and the carry is at most 1.
    have hV : num (fun k => colv s₁.mem x [.addM (o + 4 * k)]) 8 = fe s.mem x o := by
      rw [m₁]; simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]; rfl
    rw [hV, a₁] at e₂
    have hlt := fe_lt s.mem x o
    have hw := num_lt (f := fun k => wv s₂.mem x (o + 4 * k)) (n := 8) fun _ _ => BitVec.isLt _
    have h0 := le_num (f := fun k => wv s₂.mem x (o + 4 * k)) (n := 8) (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    generalize hW : num (fun k => wv s₂.mem x (o + 4 * k)) 8 = W at e₂ hw h0
    have hc2 : acc s₂ ≤ 1 := by
      rcases Nat.lt_or_ge (acc s₂) 2 with h | h
      · omega_using [h]
      · have : (2 ^ 32) ^ 8 * 2 ≤ (2 ^ 32) ^ 8 * acc s₂ := Nat.mul_le_mul_left _ h
        omega_using [this, e₂, hlt, hc']
    have hw0 : wv s₂.mem x o + 38 * acc s₂ < 2 ^ 32 := by
      rcases Nat.lt_or_ge (acc s₂) 1 with h | h
      · have := BitVec.isLt (wd s₂.mem x o); simp only [wv, wd] at this ⊢; omega_using [h, this]
      · omega_using [h, hc2, e₂, hlt, hc', h0]
    refine WP.mono (tail_ok (k₂.ctx c₁) (by omega_using [ho]) rfl hc2 hw0) fun s₃ ⟨k₃, f₃, w₃⟩ =>
      ⟨k₁.trans (k₂.trans k₃), ?_, ?_⟩
    · rw [m₁] at f₂
      exact f₂.trans (frameWiden f₃ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho]))
    · have e₃ : fe s₃.mem x o = W + 38 * acc s₂ := by
        rw [← hW]
        refine num_add0 (by decide) (by simp only [Nat.mul_zero, Nat.add_zero]; exact w₃) fun k h₁ h₂ => ?_
        show (wd s₃.mem x (o + 4 * k)).toNat = (wd s₂.mem x (o + 4 * k)).toNat
        rw [wd_frame1 f₃ hfit (by omega_using [ho]) (by omega_using [ho, h₂]) (by omega_using [h₁])]
      rw [e₃, ← fold256 W (acc s₂), e₂, Nat.add_comm]

/-- An element summed by eight columns (reading no word an earlier one
stored) and folded: the sum of the columns modulo `p`. -/
theorem linear_ok {x : BitVec 32} {s : State} (hctx : Ctx x s) (o : Nat) (ts : Nat → List Term)
    (ho : o + 32 ≤ 8192)
    (hr : ∀ k < 8, ∀ t ∈ ts k, ∀ d ∈ treads t, d + 4 ≤ 8192 ∧ (d + 4 ≤ o ∨ o + 4 * k ≤ d))
    (hb : ∀ k < 8, colv s.mem x (ts k) < 2 ^ 68)
    (hV : num (fun k => colv s.mem x (ts k)) 8 < 2 ^ 256 * 2 ^ 26) :
    WP isa (.block (linear o ts)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = num (fun k => colv s.mem x (ts k)) 8 % P := by
  have hfit := hctx.fit
  refine WP.block_append (WP.block_append ?_)
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  have k₃ : Keep s s₃ := (updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have a₃ : acc s₃ = 0 := by
    simp only [acc, v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
      u₂.other .ebx (by decide), u₁.gpr, toNat_zero32]
  have c₃ := k₃.ctx hctx
  refine WP.mono (cols_ok c₃ ts 8 ho hr (by rw [m₃]; exact hb) (by rw [a₃]; decide))
    fun s₄ ⟨k₄, f₄, e₄, _⟩ => ?_
  rw [a₃, m₃, Nat.zero_add] at e₄
  have hc : acc s₄ < 2 ^ 26 := by
    have : (2 ^ 32) ^ 8 * acc s₄ < (2 ^ 32) ^ 8 * 2 ^ 26 := by omega_using [e₄, hV]
    exact Nat.lt_of_mul_lt_mul_left this
  refine WP.mono (fold_ok (k₄.ctx c₃) ho rfl hc) fun s₅ ⟨k₅, f₅, e₅⟩ =>
    ⟨k₃.trans (k₄.trans k₅), by rw [m₃] at f₄; exact f₄.trans f₅, ?_⟩
  rw [e₅, ← fold256, ← e₄]
  rfl

end VG.Proof.Ed25519.X86
