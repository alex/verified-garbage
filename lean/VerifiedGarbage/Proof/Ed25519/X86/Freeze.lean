import VerifiedGarbage.Proof.Ed25519.X86.Ops

/-!
# Ed25519 on x86 (32-bit): the full reduction

`freeze o` leaves at `o` the element's value modulo `p`: bit 255 is folded in
as 19 (`V' < 2²⁵⁵ + 19 < 2p`), then `V' + 19 - 2²⁵⁵ = V' - p` is selected if it
is not negative, that is if bit 255 of `W = V' + 19` is set.
-/

namespace VG.Proof.Ed25519.X86

open VG.Proof.X25519
open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem shr31_toNat (w : BitVec 32) : (w >>> 31).toNat = w.toNat / 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem low31_toNat (w : BitVec 32) : (w &&& low31).toNat = w.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_and, show low31.toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- Bit 255 of the element at `o` into the accumulator as `19 b`, and cleared. -/
theorem top_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block [.mov .eax (.mem (sc (o + 28))), .shift .shr .eax 31, .mov .edx (.imm 19), .mul .edx,
      .mov .ebx (.reg .eax), .mov .ecx (.imm 0), .mov .ebp (.imm 0),
      .mov .eax (.mem (sc (o + 28))), .alu .and .eax (.imm low31), .store (sc (o + 28)) .eax]) s fun s' =>
      Keep s s' ∧ Frame [sub x (o + 28) 4] s.mem s'.mem ∧ acc s' = 19 * (wv s.mem x (o + 28) / 2 ^ 31) ∧
        wv s'.mem x (o + 28) = wv s.mem x (o + 28) % 2 ^ 31 := by
  have hfit := hc.fit
  refine Wp.wp_ldm hc.edi (hc.inRW (by omega_using [ho]) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_shr (by decide) fun s₂ u₂ _ => Wp.wp_movi fun s₃ u₃ => wp_mul fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => Wp.wp_movi fun s₆ u₆ => Wp.wp_movi fun s₇ u₇ => ?_
  have k₇ : Keep s s₇ := (updKeep u₁).trans ((updKeep u₂).trans ((updKeep u₃).trans (u₄.keep.trans
    ((updKeep u₅).trans ((updKeep u₆).trans (updKeep u₇))))))
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₇ := k₇.ctx hc
  refine Wp.wp_ldm c₇.edi (c₇.inRW (by omega_using [ho]) (by decide)) fun s₈ u₈ => ?_
  refine Wp.wp_andi fun s₉ u₉ => ?_
  have c₉ := (updKeep u₉).ctx ((updKeep u₈).ctx c₇)
  refine Wp.wp_stm c₉.edi (c₉.inW (by omega_using [ho]) (by decide)) fun s₁₀ u₁₀ => WP.block_nil ?_
  have hb : v s₄ .eax = wv s.mem x (o + 28) / 2 ^ 31 * 19 := by
    rw [u₄.eax, v, u₃.other _ (by decide), u₂.gpr, v, u₃.gpr, shr31_toNat, u₁.gpr]
    have := wv_lt s.mem x (o + 28)
    exact Nat.mod_eq_of_lt (by simp only [wv, wd] at this ⊢; show _ * 19 < _; omega_using [this])
  refine ⟨k₇.trans ((updKeep u₈).trans ((updKeep u₉).trans ⟨by rw [u₁₀.gpr], by rw [u₁₀.gpr],
    by rw [u₁₀.gpr], u₁₀.rd, u₁₀.wr⟩)), ?_, ?_, ?_⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, m₇]
    exact frame_write1 (Frame.refl _ _) hfit (by omega_using [ho]) (Nat.le_refl _) (Nat.le_refl _) _
  · simp only [acc, v, u₁₀.gpr, u₉.other .ebx (by decide), u₉.other .ecx (by decide),
      u₉.other .ebp (by decide), u₈.other .ebx (by decide), u₈.other .ecx (by decide),
      u₈.other .ebp (by decide), u₇.gpr, u₇.other .ebx (by decide), u₇.other .ecx (by decide), u₆.gpr,
      u₆.other .ebx (by decide), u₅.gpr, toNat_zero32, Nat.mul_zero, Nat.add_zero]
    simp only [v] at hb; rw [hb, Nat.mul_comm]
  · rw [u₁₀.mem, wv, wd_write_self, u₉.gpr, u₈.gpr, low31_toNat, m₇]

/-- The accumulator set to `c`. -/
theorem setAcc_ok {s : State} (c : BitVec 32) :
    WP isa (.block [.mov .ebx (.imm c), .mov .ecx (.imm 0), .mov .ebp (.imm 0)]) s fun s' =>
      Keep s s' ∧ s'.mem = s.mem ∧ acc s' = c.toNat := by
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [acc, v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
    u₂.other .ebx (by decide), u₁.gpr, toNat_zero32, Nat.mul_zero, Nat.add_zero]

/-- The mask of bit 255 of `W` in `T` into `ecx`, and the bit cleared. -/
theorem mask_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block [.mov .eax (.mem (sc (T + 28))), .shift .shr .eax 31, .mov .ecx (.imm 0),
      .alu .sub .ecx (.reg .eax), .mov .eax (.mem (sc (T + 28))), .alu .and .eax (.imm low31),
      .store (sc (T + 28)) .eax]) s fun s' =>
      Keep s s' ∧ Frame [sub x (T + 28) 4] s.mem s'.mem ∧
        s'.gpr .ecx = mask (wv s.mem x (T + 28) / 2 ^ 31) ∧
        wv s'.mem x (T + 28) = wv s.mem x (T + 28) % 2 ^ 31 := by
  have hfit := hc.fit
  refine Wp.wp_ldm hc.edi (hc.inRW (by simp only [T]; decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_shr (by decide) fun s₂ u₂ _ => Wp.wp_movi fun s₃ u₃ => Wp.wp_sub fun s₄ u₄ _ => ?_
  have k₄ : Keep s s₄ := (updKeep u₁).trans ((updKeep u₂).trans ((updKeep u₃).trans (updKeep u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ := k₄.ctx hc
  refine Wp.wp_ldm c₄.edi (c₄.inRW (by simp only [T]; decide) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_andi fun s₆ u₆ => ?_
  have c₆ := (updKeep u₆).ctx ((updKeep u₅).ctx c₄)
  refine Wp.wp_stm c₆.edi (c₆.inW (by simp only [T]; decide) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  refine ⟨k₄.trans ((updKeep u₅).trans ((updKeep u₆).trans ⟨by rw [u₇.gpr], by rw [u₇.gpr],
    by rw [u₇.gpr], u₇.rd, u₇.wr⟩)), ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, m₄]
    exact frame_write1 (Frame.refl _ _) hfit (by simp only [T]; decide) (Nat.le_refl _) (Nat.le_refl _) _
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .eax (by decide),
      mask]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [u₂.gpr, shr31_toNat, u₁.gpr, BitVec.toNat_ofNat]
    have := wv_lt s.mem x (T + 28)
    simp only [wv, wd] at this ⊢
    omega_using [this]
  · rw [u₇.mem, wv, wd_write_self, u₆.gpr, u₅.gpr, low31_toNat, m₄]

/-- The words below `n` of the element at `o` selected from `T` if `g = 1`. -/
structure SelInv (x : BitVec 32) (s₀ : State) (o g n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  ecx : s.gpr .ecx = s₀.gpr .ecx
  frame : Frame [sub x o (4 * n)] s₀.mem s.mem
  done : ∀ j < n, wd s.mem x (o + 4 * j) = if g = 1 then wd s₀.mem x (T + 4 * j) else wd s₀.mem x (o + 4 * j)

theorem select_step {x : BitVec 32} {s₀ s : State} (hc : Ctx x s) {o g n : Nat} (ho : Below o)
    (hg : g ≤ 1) (hm : s₀.gpr .ecx = mask g) (hn : n < 8) (h : SelInv x s₀ o g n s) :
    WP isa (.block [.mov .eax (.mem (sc (o + 4 * n))), .mov .edx (.mem (sc (T + 4 * n))),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (sc (o + 4 * n)) .eax]) s (SelInv x s₀ o g (n + 1)) := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_ldm hc.edi (hc.inRW (by omega_using [ho, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_ldm c₁.edi (c₁.inRW (by simp only [T]; omega_using [hn]) (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_xor fun s₃ u₃ => Wp.wp_and fun s₄ u₄ => Wp.wp_xor fun s₅ u₅ => ?_
  have k₅ : Keep s s₅ := (updKeep u₁).trans ((updKeep u₂).trans ((updKeep u₃).trans ((updKeep u₄).trans
    (updKeep u₅))))
  have c₅ := k₅.ctx hc
  refine Wp.wp_stm c₅.edi (c₅.inW (by omega_using [ho, hn]) (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have eo : s₁.gpr .eax = wd s₀.mem x (o + 4 * n) := by
    rw [u₁.gpr]; exact wd_frame1 h.frame hfit (by omega_using [ho, hn]) (by omega_using [ho, hn])
      (.inr (Nat.le_refl _))
  have eT : s₂.gpr .edx = wd s₀.mem x (T + 4 * n) := by
    rw [u₂.gpr, u₁.mem]; exact wd_frame1 h.frame hfit (by omega_using [ho, hn])
      (by simp only [T]; omega_using [hn]) (.inr (by simp only [T]; omega_using [ho]))
  have v₅ : s₅.gpr .eax = if g = 1 then wd s₀.mem x (T + 4 * n) else wd s₀.mem x (o + 4 * n) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.other .eax (by decide),
      eo, eT, u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide), h.ecx, hm,
      BitVec.xor_comm (wd s₀.mem x (T + 4 * n))]
    exact (sel_mask _ _ hg).1
  refine ⟨h.keep.trans (k₅.trans ⟨by rw [u₆.gpr], by rw [u₆.gpr], by rw [u₆.gpr], u₆.rd, u₆.wr⟩),
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx], ?_, fun j hj => ?_⟩
  · rw [u₆.mem, m₅]
    exact frame_write1 (frameWiden h.frame hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₆.mem, m₅]
    by_cases e : j = n
    · subst e; rw [wd_write_self, v₅]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact h.done j (by omega_using [hj, e])

theorem selects_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx x s₀) {o g : Nat} (ho : Below o)
    (hg : g ≤ 1) (hm : s₀.gpr .ecx = mask g) : ∀ n ≤ 8, ∀ s, SelInv x s₀ o g 0 s →
    WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.mem (sc (o + 4 * k))), .mov .edx (.mem (sc (T + 4 * k))), .alu .xor .edx (.reg .eax),
        .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc (o + 4 * k)) .eax])) s
      (SelInv x s₀ o g n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (selects_ok hc₀ ho hg hm n (by omega_using [hn]) s h)
      fun s₁ h₁ => select_step (h₁.keep.ctx hc₀) ho hg hm (by omega_using [hn]) h₁)

/-- The top word of an element. -/
theorem num_top (f : Nat → Nat) : num f 8 = num f 7 + 2 ^ 224 * f 7 := rfl

theorem num7_lt {f : Nat → Nat} (h : ∀ k < 7, f k < 2 ^ 32) : num f 7 < 2 ^ 224 := num_lt h

/-- The element with bit 255 folded in as 19. -/
theorem fold_top {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) :
    num f 8 % 2 ^ 255 = num f 7 + 2 ^ 224 * (f 7 % 2 ^ 31) ∧ num f 8 / 2 ^ 255 = f 7 / 2 ^ 31 := by
  have h7 := num7_lt fun k hk => h k (by omega_using [hk])
  have hf := h 7 (by decide)
  rw [num_top]
  have e := Nat.div_add_mod (f 7) (2 ^ 31)
  generalize f 7 / 2 ^ 31 = q at e ⊢
  generalize hr : f 7 % 2 ^ 31 = r at e ⊢
  have hr' : r < 2 ^ 31 := hr ▸ Nat.mod_lt _ (by decide)
  generalize num f 7 = N at h7 ⊢
  rw [← e]
  omega_using [h7, hr']

theorem freeze_eq (o : Nat) : freeze o =
    ([.mov .eax (.mem (sc (o + 28))), .shift .shr .eax 31, .mov .edx (.imm 19), .mul .edx,
      .mov .ebx (.reg .eax), .mov .ecx (.imm 0), .mov .ebp (.imm 0),
      .mov .eax (.mem (sc (o + 28))), .alu .and .eax (.imm low31), .store (sc (o + 28)) .eax] : List Instr) ++
    (cols o 8 (fun k => [.addM (o + 4 * k)]) ++
    (([.mov .ebx (.imm 19), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] : List Instr) ++
    (cols T 8 (fun k => [.addM (o + 4 * k)]) ++
    (([.mov .eax (.mem (sc (T + 28))), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
      .mov .eax (.mem (sc (T + 28))), .alu .and .eax (.imm low31), .store (sc (T + 28)) .eax] : List Instr) ++
    (List.range 8).flatMap fun k =>
      [.mov .eax (.mem (sc (o + 4 * k))), .mov .edx (.mem (sc (T + 4 * k))), .alu .xor .edx (.reg .eax),
        .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc (o + 4 * k)) .eax])))) := by
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]

theorem colv_addM (m : Mem) (x : BitVec 32) (d : Nat) : colv m x [.addM d] = wv m x d := by
  simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The element at `o` reduced fully, in place. -/
theorem freeze_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : isSlot o = true) :
    WP isa (.block (freeze o)) s fun s' => Keep s s' ∧ Frame [sub x o 32, sub x T 32] s.mem s'.mem ∧
      fe s'.mem x o = fe s.mem x o % P := by
  have hfit := hc.fit
  have hob := slot_below ho
  simp only [Below, T] at hob
  rw [freeze_eq]
  -- The words of the element on entry.
  have hV := fold_top (f := fun k => wv s.mem x (o + 4 * k)) fun k _ => wv_lt _ _ _
  have hVa : fe s.mem x o % 2 ^ 255 = num (fun k => wv s.mem x (o + 4 * k)) 7 +
      2 ^ 224 * (wv s.mem x (o + 28) % 2 ^ 31) := hV.1
  have hVb : fe s.mem x o / 2 ^ 255 = wv s.mem x (o + 28) / 2 ^ 31 := hV.2
  refine WP.block_append (WP.mono (top_ok hc (by omega_using [hob])) fun s₁ ⟨k₁, f₁, a₁, w₁⟩ => ?_)
  have c₁ := k₁.ctx hc
  -- `V1`: the element without bit 255.
  have e₁ : fe s₁.mem x o = fe s.mem x o % 2 ^ 255 := by
    have n7 : num (fun k => wv s₁.mem x (o + 4 * k)) 7 = num (fun k => wv s.mem x (o + 4 * k)) 7 :=
      num_congr fun j hj => by
        show (wd s₁.mem x (o + 4 * j)).toNat = (wd s.mem x (o + 4 * j)).toNat
        rw [wd_frame1 f₁ hfit (by omega_using [hob]) (by omega_using [hob, hj]) (.inl (by omega_using [hj]))]
    rw [hVa, ← w₁, ← n7]
    rfl
  have hb : wv s.mem x (o + 28) / 2 ^ 31 ≤ 1 := by
    have := wv_lt s.mem x (o + 28); simp only [wv, wd] at this ⊢; omega_using [this]
  refine WP.block_append (WP.mono (cols_ok c₁ (fun k => [.addM (o + 4 * k)]) 8 (by omega_using [hob])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [a₁]; omega_using [hb])) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_)
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hob, hk], .inr (Nat.le_refl _)⟩
  · rw [colv_addM]; have := wv_lt s₁.mem x (o + 4 * k); omega_using [this]
  have c₂ := k₂.ctx c₁
  -- `V' = V1 + 19 b`.
  have hs₂ : num (fun k => colv s₁.mem x [.addM (o + 4 * k)]) 8 = fe s₁.mem x o :=
    num_congr fun k _ => colv_addM _ _ _
  rw [hs₂, a₁, e₁] at e₂
  have hV1 : fe s.mem x o % 2 ^ 255 < 2 ^ 255 := Nat.mod_lt _ (by decide)
  have eV' : fe s₂.mem x o = 19 * (fe s.mem x o / 2 ^ 255) + fe s.mem x o % 2 ^ 255 := by
    rw [hVb]
    change num _ 8 + (2 ^ 32) ^ 8 * acc s₂ = _ at e₂
    have : acc s₂ = 0 := by
      rcases Nat.eq_zero_or_pos (acc s₂) with h | h
      · exact h
      · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h; omega_using [this, e₂, hV1, hb]
    rw [this, Nat.mul_zero, Nat.add_zero] at e₂
    exact e₂
  refine WP.block_append (WP.mono (setAcc_ok (s := s₂) 19) fun s₃ ⟨k₃, m₃, a₃⟩ => ?_)
  have c₃ := k₃.ctx c₂
  refine WP.block_append (WP.mono (cols_ok c₃ (fun k => [.addM (o + 4 * k)]) 8 (by simp only [T]; decide)
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [a₃]; decide)) fun s₄ ⟨k₄, f₄, e₄, _⟩ => ?_)
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hob, hk], .inl (by simp only [T]; omega_using [hob, hk])⟩
  · rw [colv_addM]; have := wv_lt s₃.mem x (o + 4 * k); omega_using [this]
  have c₄ := k₄.ctx c₃
  -- `W = V' + 19`.
  have hs₄ : num (fun k => colv s₃.mem x [.addM (o + 4 * k)]) 8 = fe s₂.mem x o := by
    rw [m₃]; exact num_congr fun k _ => colv_addM _ _ _
  rw [hs₄, a₃, show (19 : BitVec 32).toNat = 19 from rfl] at e₄
  have eW : num (fun k => wv s₄.mem x (T + 4 * k)) 8 = fe s₂.mem x o + 19 := by
    change num _ 8 + (2 ^ 32) ^ 8 * acc s₄ = _ at e₄
    have : acc s₄ = 0 := by
      rcases Nat.eq_zero_or_pos (acc s₄) with h | h
      · exact h
      · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h
        rw [eV'] at e₄; omega_using [this, e₄, hV1, hb, hVb]
    rw [this, Nat.mul_zero, Nat.add_zero] at e₄
    rw [e₄]; omega_using []
  have hW := fold_top (f := fun k => wv s₄.mem x (T + 4 * k)) fun k _ => wv_lt _ _ _
  have hWa : num (fun k => wv s₄.mem x (T + 4 * k)) 8 % 2 ^ 255 = num (fun k => wv s₄.mem x (T + 4 * k)) 7 +
      2 ^ 224 * (wv s₄.mem x (T + 28) % 2 ^ 31) := hW.1
  have hWb : num (fun k => wv s₄.mem x (T + 4 * k)) 8 / 2 ^ 255 = wv s₄.mem x (T + 28) / 2 ^ 31 := hW.2
  refine WP.block_append (WP.mono (mask_ok c₄) fun s₅ ⟨k₅, f₅, m₅, w₅⟩ => ?_)
  have c₅ := k₅.ctx c₄
  have hg : wv s₄.mem x (T + 28) / 2 ^ 31 ≤ 1 := by
    have := wv_lt s₄.mem x (T + 28); simp only [wv, wd] at this ⊢; omega_using [this]
  have hoT : ∀ j < 8, wd s₅.mem x (o + 4 * j) = wd s₂.mem x (o + 4 * j) := fun j hj => by
    rw [wd_frame1 f₅ hfit (by simp only [T]; decide) (by omega_using [hob, hj])
      (.inl (by simp only [T]; omega_using [hob, hj])), wd_frame1 f₄ hfit (by simp only [T]; decide)
      (by omega_using [hob, hj]) (.inl (by simp only [T]; omega_using [hob, hj])), m₃]
  -- `T` now holds `W mod 2²⁵⁵`.
  have eT : num (fun k => wv s₅.mem x (T + 4 * k)) 8 = (fe s₂.mem x o + 19) % 2 ^ 255 := by
    have n7 : num (fun k => wv s₅.mem x (T + 4 * k)) 7 = num (fun k => wv s₄.mem x (T + 4 * k)) 7 :=
      num_congr fun j hj => by
        show (wd s₅.mem x (T + 4 * j)).toNat = (wd s₄.mem x (T + 4 * j)).toNat
        rw [wd_frame1 f₅ hfit (by simp only [T]; decide) (by simp only [T]; omega_using [hj])
          (.inl (by simp only [T]; omega_using [hj]))]
    rw [← eW, hWa, ← w₅, ← n7]
    rfl
  refine WP.mono (selects_ok c₅ (o := o) (g := wv s₄.mem x (T + 28) / 2 ^ 31) (by simp only [Below, T]; omega_using [hob]) hg m₅ 8
    (Nat.le_refl _) s₅ ⟨Keep.refl _, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun s₆ h₆ => ⟨k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans h₆.keep)))), ?_, ?_⟩
  · -- Everything written is in the element and `T`.
    have w1 : ∀ {m m' : Mem} {a n : Nat}, Frame [sub x a n] m m' →
        o ≤ a → a + n ≤ o + 32 → a < 8192 → Frame [sub x o 32, sub x T 32] m m' := fun hf h1 h2 h3 =>
      (frameWiden hf hfit h1 h2 h3).mono (fun r hr => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
    have w2 : ∀ {m m' : Mem} {a n : Nat}, Frame [sub x a n] m m' →
        T ≤ a → a + n ≤ T + 32 → a < 8192 → Frame [sub x o 32, sub x T 32] m m' := fun hf h1 h2 h3 =>
      (frameWiden hf hfit h1 h2 h3).mono (fun r hr => List.mem_cons_of_mem _ hr)
    rw [m₃] at f₄
    exact (w1 f₁ (by omega) (by omega) (by omega_using [hob])).trans
      ((w1 f₂ (by omega) (by omega) (by omega_using [hob])).trans
      ((w2 f₄ (by decide) (by decide) (by decide)).trans
      ((w2 f₅ (by simp only [T]; decide) (by simp only [T]; decide) (by simp only [T]; decide)).trans
      (w1 h₆.frame (by omega) (by omega) (by omega_using [hob])))))
  · -- The selection is the value modulo `p`.
    have e₆ : fe s₆.mem x o = if wv s₄.mem x (T + 28) / 2 ^ 31 = 1 then (fe s₂.mem x o + 19) % 2 ^ 255
        else fe s₂.mem x o := by
      rw [← eT]
      split
      · exact num_congr fun j hj => by
          show (wd s₆.mem x (o + 4 * j)).toNat = (wd s₅.mem x (T + 4 * j)).toNat
          rw [h₆.done j hj, ite_eq_left ‹_›]
      · exact num_congr fun j hj => by
          show (wd s₆.mem x (o + 4 * j)).toNat = (wd s₂.mem x (o + 4 * j)).toNat
          rw [h₆.done j hj, ite_eq_right ‹_›, hoT j hj]
    have hWb' : wv s₄.mem x (T + 28) / 2 ^ 31 = (fe s₂.mem x o + 19) / 2 ^ 255 := by
      rw [← eW, hWb]
    rw [e₆, hWb']
    have hmod : fe s₂.mem x o % P = fe s.mem x o % P := by
      rw [eV', Nat.add_comm, ← fold255, Nat.mul_comm, Nat.mod_add_div']
    rw [← hmod]
    have hlt : fe s₂.mem x o < P + 38 := by rw [eV']; simp only [P]; omega_using [hV1, hb, hVb]
    simp only [P] at hlt ⊢
    split <;> rename_i hsplit <;> omega_using [hlt, hsplit]

end VG.Proof.Ed25519.X86
