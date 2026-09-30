import VerifiedGarbage.Proof.X25519.X86.Arith

/-!
# X25519 on x86 (32-bit): sequences of field operations

Untrusted: everything here is checked by Lean. The elements the ladder and the
inversion compute with are at the *slots* of the working space (offsets
`288 + 32 i` below `T`), and their values `F m x q` in `GF(p)`. A sequence of
operations (`ops`) leaves in each slot the value of an evaluation of the
operations on the values of the slots (`run`), and changes no memory
outside the slots and `T`. Also: `copy`, and `cswap` by a mask.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The value in `GF(p)` of the element at `[x + q]`. -/
def F (m : Mem) (x : BitVec 32) (q : Nat) : Fe := toFe (fe m x q)

/-- The slots: offsets `288 + 32 i` below `T`. -/
def isSlot (q : Nat) : Bool := 288 ≤ q && q < T && (q - 288) % 32 == 0

theorem slot_below {q : Nat} (h : isSlot q = true) : Below q := by
  simp only [isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Below, T] at h ⊢; omega_using [h]

theorem slot_ge {q : Nat} (h : isSlot q = true) : 288 ≤ q := by
  simp only [isSlot, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem slot_apart {o q : Nat} (ho : isSlot o = true) (hq : isSlot q = true) : Apart o q := by
  simp only [isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho hq
  simp only [Apart, T] at ho hq ⊢; omega_using [ho, hq]

theorem slot_ne {o q : Nat} (ho : isSlot o = true) (hq : isSlot q = true) (h : q ≠ o) :
    q + 32 ≤ o ∨ o + 32 ≤ q := by
  simp only [isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho hq
  simp only [T] at ho hq; omega_using [ho, hq, h]

/-! ## Copies -/

theorem copy_step {x : BitVec 32} {s₀ s : State} (hc : Ctx x s) {o a n : Nat} (ho : Below o)
    (ha : Below a) (hoa : Apart o a) (hn : n < 8) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = wd s₀.mem x (a + 4 * j)) :
    WP isa (.block [.mov .eax (.mem (sc (a + 4 * n))), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = wd s₀.mem x (a + 4 * j) := by
  simp only [Below, T] at ho ha
  have hfit := hc.fit
  refine Wp.wp_ldm hc.edi (hc.inRW (by omega_using [ha, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have hr : wd s.mem x (a + 4 * n) = wd s₀.mem x (a + 4 * n) :=
    wd_frame1 hf hfit (by omega_using [ho, hn]) (by omega_using [ha, hn])
      (apart_read hoa (Nat.le_refl _) hn)
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self]; exact hr
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem copies_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a : Nat} (ho : Below o) (ha : Below a)
    (hoa : Apart o a) : ∀ n ≤ 8,
    WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (sc (a + 4 * k))),
      .store (sc (o + 4 * k)) .eax])) s fun s' =>
      Keep s s' ∧ Frame [sub x o (4 * n)] s.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = wd s.mem x (a + 4 * j)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (copies_ok hc ho ha hoa n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      copy_step (k₁.ctx hc) ho ha hoa (by omega_using [hn]) k₁ f₁ w₁)

theorem copy_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o a : Nat} (ho : Below o) (ha : Below a)
    (hoa : Apart o a) :
    WP isa (.block (copy o a)) s fun s' =>
      Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧ fe s'.mem x o = fe s.mem x a :=
  WP.mono (copies_ok hc ho ha hoa 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ =>
    ⟨k, f, num_congr fun j hj => by
      show (wd _ x (o + 4 * j)).toNat = (wd _ x (a + 4 * j)).toNat; rw [w j hj]⟩

/-! ## Conditional swaps -/

/-- The mask of `sw ∈ {0, 1}`. -/
def mask (sw : Nat) : BitVec 32 := 0 - BitVec.ofNat 32 sw

theorem sel_mask (X Y : BitVec 32) {sw : Nat} (h : sw ≤ 1) :
    X ^^^ ((X ^^^ Y) &&& mask sw) = (if sw = 1 then Y else X) ∧
      Y ^^^ ((X ^^^ Y) &&& mask sw) = (if sw = 1 then X else Y) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
  · simp only [mask, BitVec.ofNat_eq_ofNat, BitVec.sub_zero, BitVec.and_zero, BitVec.xor_zero]
    exact ⟨rfl, rfl⟩
  · have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
    simp only [mask, this, BitVec.and_allOnes, ite_true]
    refine ⟨?_, ?_⟩
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm X Y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The words below `n` of the elements at `[x + X]` and `[x + Y]` swapped if
`sw = 1`, the others as on entry. -/
structure SwapInv (x : BitVec 32) (s₀ : State) (X Y sw n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  ecx : s.gpr .ecx = s₀.gpr .ecx
  frame : Frame [sub x X 32, sub x Y 32] s₀.mem s.mem
  done : ∀ j < n, wd s.mem x (X + 4 * j) = (if sw = 1 then wd s₀.mem x (Y + 4 * j) else wd s₀.mem x (X + 4 * j)) ∧
    wd s.mem x (Y + 4 * j) = (if sw = 1 then wd s₀.mem x (X + 4 * j) else wd s₀.mem x (Y + 4 * j))
  todo : ∀ j < 8, n ≤ j → wd s.mem x (X + 4 * j) = wd s₀.mem x (X + 4 * j) ∧
    wd s.mem x (Y + 4 * j) = wd s₀.mem x (Y + 4 * j)

theorem cswap_step {x : BitVec 32} {s₀ s : State} (hc : Ctx x s) {X Y sw n : Nat} (hX : Below X)
    (hY : Below Y) (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s₀.gpr .ecx = mask sw)
    (hn : n < 8) (h : SwapInv x s₀ X Y sw n s) :
    WP isa (.block [.mov .eax (.mem (sc (X + 4 * n))), .mov .edx (.mem (sc (Y + 4 * n))), .mov .ebx (.reg .eax),
      .alu .xor .ebx (.reg .edx), .alu .and .ebx (.reg .ecx), .alu .xor .eax (.reg .ebx),
      .alu .xor .edx (.reg .ebx), .store (sc (X + 4 * n)) .eax, .store (sc (Y + 4 * n)) .edx]) s
      (SwapInv x s₀ X Y sw (n + 1)) := by
  simp only [Below, T] at hX hY
  have hfit := hc.fit
  refine Wp.wp_ldm hc.edi (hc.inRW (by omega_using [hX, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_ldm c₁.edi (c₁.inRW (by omega_using [hY, hn]) (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_mov fun s₃ u₃ => Wp.wp_xor fun s₄ u₄ => Wp.wp_and fun s₅ u₅ => Wp.wp_xor fun s₆ u₆ =>
    Wp.wp_xor fun s₇ u₇ => ?_
  have k₇ : Keep s s₇ := (updKeep u₁).trans ((updKeep u₂).trans ((updKeep u₃).trans ((updKeep u₄).trans
    ((updKeep u₅).trans ((updKeep u₆).trans (updKeep u₇))))))
  have c₇ := k₇.ctx hc
  refine Wp.wp_stm c₇.edi (c₇.inW (by omega_using [hX, hn]) (by decide)) fun s₈ u₈ => ?_
  have c₈ : Ctx x s₈ := c₇.keep (by rw [u₈.gpr]) u₈.wr
  refine Wp.wp_stm c₈.edi (c₈.inW (by omega_using [hY, hn]) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  -- The values.
  have m₇ : s₇.mem = s.mem := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₇ : s₇.gpr .ecx = s.gpr .ecx := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ⟨tX, tY⟩ := h.todo n hn (Nat.le_refl _)
  have eX : s₁.gpr .eax = wd s₀.mem x (X + 4 * n) := by rw [u₁.gpr]; exact tX
  have eY : s₂.gpr .edx = wd s₀.mem x (Y + 4 * n) := by rw [u₂.gpr, u₁.mem]; exact tY
  have ed : s₅.gpr .ebx = (wd s₀.mem x (X + 4 * n) ^^^ wd s₀.mem x (Y + 4 * n)) &&& mask sw := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide),
      u₃.other .edx (by decide), u₂.other .eax (by decide), eX, eY, u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), h.ecx, hm]
  have v₆ : s₆.gpr .eax = if sw = 1 then wd s₀.mem x (Y + 4 * n) else wd s₀.mem x (X + 4 * n) := by
    rw [u₆.gpr, ed, u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), eX]
    exact (sel_mask _ _ hsw).1
  have v₇ : s₇.gpr .edx = if sw = 1 then wd s₀.mem x (X + 4 * n) else wd s₀.mem x (Y + 4 * n) := by
    rw [u₇.gpr, u₆.other .ebx (by decide), ed, u₆.other .edx (by decide),
      u₅.other .edx (by decide), u₄.other .edx (by decide), u₃.other .edx (by decide), eY]
    exact (sel_mask _ _ hsw).2
  have eax₈ : s₇.gpr .eax = s₆.gpr .eax := u₇.other _ (by decide)
  have hsep : ∀ j < 8, ∀ k < 8, X + 4 * j + 4 ≤ Y + 4 * k ∨ Y + 4 * k + 4 ≤ X + 4 * j := fun j hj k hk => by
    omega_using [hXY, hj, hk]
  have wX : ∀ j < 8, wd s₉.mem x (X + 4 * j) =
      if j = n then (if sw = 1 then wd s₀.mem x (Y + 4 * n) else wd s₀.mem x (X + 4 * n))
      else wd s.mem x (X + 4 * j) := fun j hj => by
    rw [u₉.mem, u₈.mem, u₈.gpr, v₇, wd_write_ne _ _ (by omega_using [hfit, hX, hj])
      (by omega_using [hfit, hY, hn]) (hsep j hj n hn), eax₈, v₆, m₇]
    by_cases e : j = n
    · subst e; rw [wd_write_self]; simp only [↓reduceIte]
    · rw [wd_write_ne _ _ (by omega_using [hfit, hX, hj]) (by omega_using [hfit, hX, hn])
        (by omega_using [e]), ite_eq_right e]
  have wY : ∀ j < 8, wd s₉.mem x (Y + 4 * j) =
      if j = n then (if sw = 1 then wd s₀.mem x (X + 4 * n) else wd s₀.mem x (Y + 4 * n))
      else wd s.mem x (Y + 4 * j) := fun j hj => by
    rw [u₉.mem, u₈.mem, u₈.gpr, v₇]
    by_cases e : j = n
    · subst e; rw [wd_write_self]; simp only [↓reduceIte]
    · rw [wd_write_ne _ _ (by omega_using [hfit, hY, hj]) (by omega_using [hfit, hY, hn])
        (by omega_using [e]), ite_eq_right e, wd_write_ne _ _ (by omega_using [hfit, hY, hj])
        (by omega_using [hfit, hX, hn]) ((hsep n hn j hj).symm), m₇]
  refine ⟨h.keep.trans (k₇.trans ⟨by rw [u₉.gpr, u₈.gpr], by rw [u₉.gpr, u₈.gpr], by rw [u₉.gpr, u₈.gpr],
    by rw [u₉.rd, u₈.rd], by rw [u₉.wr, u₈.wr]⟩), by rw [u₉.gpr, u₈.gpr, ecx₇, h.ecx], ?_, fun j hj => ?_,
    fun j hj hnj => ?_⟩
  · rw [u₉.mem, u₈.mem, m₇]
    refine (h.frame.writeW List.mem_cons_self _ ?_).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_
    · exact sub_contains (by omega_using [hfit, hX]) (by omega_using []) (by omega_using [hn]) (by decide)
    · exact sub_contains (by omega_using [hfit, hY]) (by omega_using []) (by omega_using [hn]) (by decide)
  · rw [wX j (by omega_using [hj, hn]), wY j (by omega_using [hj, hn])]
    by_cases e : j = n
    · subst e; simp only [↓reduceIte, and_self]
    · simp only [ite_eq_right e]; exact h.done j (by omega_using [hj, e])
  · rw [wX j hj, wY j hj, ite_eq_right (by omega_using [hnj]), ite_eq_right (by omega_using [hnj])]
    exact h.todo j hj (by omega_using [hnj])

theorem cswaps_ok {x : BitVec 32} {s₀ : State} {X Y sw : Nat} (hX : Below X) (hY : Below Y)
    (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s₀.gpr .ecx = mask sw) (hc₀ : Ctx x s₀) :
    ∀ n ≤ 8, ∀ s, SwapInv x s₀ X Y sw 0 s →
    WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.mem (sc (X + 4 * k))), .mov .edx (.mem (sc (Y + 4 * k))), .mov .ebx (.reg .eax),
        .alu .xor .ebx (.reg .edx), .alu .and .ebx (.reg .ecx), .alu .xor .eax (.reg .ebx),
        .alu .xor .edx (.reg .ebx), .store (sc (X + 4 * k)) .eax, .store (sc (Y + 4 * k)) .edx])) s
      (SwapInv x s₀ X Y sw n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (cswaps_ok hX hY hXY hsw hm hc₀ n (by omega_using [hn]) s h)
      fun s₁ h₁ => cswap_step (h₁.keep.ctx hc₀) hX hY hXY hsw hm (by omega_using [hn]) h₁)

/-- `cswap X Y` with the mask of `sw` in `ecx`. -/
theorem cswap_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {X Y sw : Nat} (hX : Below X) (hY : Below Y)
    (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s.gpr .ecx = mask sw) :
    WP isa (.block (cswap X Y)) s fun s' => Keep s s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [sub x X 32, sub x Y 32] s.mem s'.mem ∧
      fe s'.mem x X = (if sw = 1 then fe s.mem x Y else fe s.mem x X) ∧
      fe s'.mem x Y = (if sw = 1 then fe s.mem x X else fe s.mem x Y) := by
  refine WP.mono (cswaps_ok hX hY hXY hsw hm hc 8 (Nat.le_refl _) s ⟨Keep.refl _, rfl, Frame.refl _ _,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => ⟨rfl, rfl⟩⟩) fun s' h =>
    ⟨h.keep, h.ecx, h.frame, ?_, ?_⟩
  · by_cases e : sw = 1
    · rw [ite_eq_left e]
      exact num_congr fun j hj => by
        show (wd _ x (X + 4 * j)).toNat = (wd _ x (Y + 4 * j)).toNat; rw [(h.done j hj).1, ite_eq_left e]
    · rw [ite_eq_right e]
      exact num_congr fun j hj => by
        show (wd _ x (X + 4 * j)).toNat = (wd _ x (X + 4 * j)).toNat; rw [(h.done j hj).1, ite_eq_right e]
  · by_cases e : sw = 1
    · rw [ite_eq_left e]
      exact num_congr fun j hj => by
        show (wd _ x (Y + 4 * j)).toNat = (wd _ x (X + 4 * j)).toNat; rw [(h.done j hj).2, ite_eq_left e]
    · rw [ite_eq_right e]
      exact num_congr fun j hj => by
        show (wd _ x (Y + 4 * j)).toNat = (wd _ x (Y + 4 * j)).toNat; rw [(h.done j hj).2, ite_eq_right e]

/-! ## Sequences of operations -/

/-- An operation's output. -/
def opOut : Op → Nat
  | .mul o _ _ | .mulSmall o _ | .add o _ _ | .sub o _ _ | .copy o _ => o

/-- An operation's inputs. -/
def opIns : Op → List Nat
  | .mul _ a b | .add _ a b | .sub _ a b => [a, b]
  | .mulSmall _ a | .copy _ a => [a]

/-- An operation on slots. -/
def opValid (op : Op) : Bool := isSlot (opOut op) && (opIns op).all isSlot

/-- An operation's result, for the values `E` of the slots. -/
def opVal (op : Op) (E : Nat → Fe) : Fe :=
  match op with
  | .mul _ a b => E a * E b
  | .mulSmall _ a => a24 * E a
  | .add _ a b => E a + E b
  | .sub _ a b => E a - E b
  | .copy _ a => E a

/-- The values of the slots after a sequence of operations. -/
def run : List Op → (Nat → Fe) → Nat → Fe
  | [], E => E
  | op :: l, E => run l (Function.update E (opOut op) (opVal op E))

theorem opVal_congr {E E' : Nat → Fe} (op : Op) (h : ∀ q ∈ opIns op, E q = E' q) : opVal op E = opVal op E' := by
  cases op <;> simp only [opIns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [opVal, h]

theorem run_congr (l : List Op) (hv : ∀ op ∈ l, opValid op = true) :
    ∀ {E E' : Nat → Fe}, (∀ q, isSlot q = true → E q = E' q) → ∀ q, isSlot q = true → run l E q = run l E' q := by
  induction l with
  | nil => exact fun h q hq => h q hq
  | cons op l ih =>
    intro E E' h q hq
    have hvo := hv op List.mem_cons_self
    simp only [opValid, Bool.and_eq_true, List.all_eq_true] at hvo
    refine ih (fun o ho => hv o (List.mem_cons_of_mem _ ho)) (fun r hr => ?_) q hq
    by_cases e : r = opOut op
    · subst e; simp only [Function.update_self]
      exact opVal_congr op fun q hq => h q (hvo.2 q hq)
    · simp only [Function.update_of_ne e]; exact h r hr

theorem op_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (op : Op) (hv : opValid op = true) :
    WP isa (.block op.code) s fun s' => Keep s s' ∧ Frame [sub x 288 640] s.mem s'.mem ∧
      ∀ q, isSlot q = true → F s'.mem x q = Function.update (F s.mem x) (opOut op) (opVal op (F s.mem x)) q := by
  have hfit := hc.fit
  simp only [opValid, Bool.and_eq_true, List.all_eq_true] at hv
  obtain ⟨ho, hi⟩ := hv
  have hob := slot_below ho; have ho' := slot_ge ho
  simp only [Below, T] at hob
  -- An element outside the output's region (and `T`'s).
  have other : ∀ {m m' : Mem}, Frame [sub x (opOut op) 32, sub x T 64] m m' → ∀ q, isSlot q = true →
      q ≠ (opOut op) → F m' x q = F m x q := fun {m m'} hf q hq hne => by
    have hqb := slot_below hq; simp only [Below, T] at hqb
    have hs := slot_ne ho hq hne
    simp only [F]
    refine congrArg toFe (fe_frame fun k hk => wd_frame hf fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega_using [hfit, hqb, hk]) (by omega_using [hfit, hob]) (by omega_using [hs, hk])
    · exact sub_disj (by omega_using [hfit, hqb, hk]) (by simp only [T]; omega_using [hfit])
        (by simp only [T]; omega_using [hqb, hk])
  have frame1 : ∀ {m m' : Mem}, Frame [sub x (opOut op) 32] m m' → Frame [sub x (opOut op) 32, sub x T 64] m m' :=
    fun hf => hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have wide : ∀ {m m' : Mem}, Frame [sub x (opOut op) 32, sub x T 64] m m' → Frame [sub x 288 640] m m' :=
    fun hf => hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_sub hfit ho' (by omega_using [hob]) (by omega_using [hob])
      · exact sub_sub hfit (by simp only [T]; omega_using []) (by simp only [T]; omega_using [])
          (by simp only [T]; omega_using [])⟩
  have fin : ∀ s', Keep s s' → Frame [sub x (opOut op) 32, sub x T 64] s.mem s'.mem →
      F s'.mem x (opOut op) = opVal op (F s.mem x) →
      Keep s s' ∧ Frame [sub x 288 640] s.mem s'.mem ∧
        ∀ q, isSlot q = true → F s'.mem x q = Function.update (F s.mem x) (opOut op) (opVal op (F s.mem x)) q :=
    fun s' k f e => ⟨k, wide f, fun q hq => by
      by_cases hq' : q = (opOut op)
      · subst hq'; rw [Function.update_self]; exact e
      · rw [Function.update_of_ne hq']; exact other f q hq hq'⟩
  cases op with
  | mul o a b =>
    simp only [opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (mul_ok hc (slot_below ho) (slot_below hi.1) (slot_below hi.2)) fun s' ⟨k, f, e⟩ =>
      fin s' k f (toFe_mul e)
  | mulSmall o a =>
    simp only [opIns, List.mem_singleton, forall_eq] at hi
    exact WP.mono (mulSmall_ok hc (slot_below ho) (slot_below hi) (slot_apart ho hi)) fun s' ⟨k, f, e⟩ =>
      fin s' k (frame1 f) (toFe_a24 e)
  | add o a b =>
    simp only [opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (add_ok hc (slot_below ho) (slot_below hi.1) (slot_below hi.2) (slot_apart ho hi.1)
      (slot_apart ho hi.2)) fun s' ⟨k, f, e⟩ => fin s' k (frame1 f) (toFe_add e)
  | sub o a b =>
    simp only [opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (sub_ok hc (slot_below ho) (slot_below hi.1) (slot_below hi.2) (slot_apart ho hi.1)
      (slot_apart ho hi.2)) fun s' ⟨k, f, e⟩ => fin s' k (frame1 f) (toFe_sub e)
  | copy o a =>
    simp only [opIns, List.mem_singleton, forall_eq] at hi
    exact WP.mono (copy_ok hc (slot_below ho) (slot_below hi) (slot_apart ho hi)) fun s' ⟨k, f, e⟩ =>
      fin s' k (frame1 f) (by simp only [F, opVal, opOut]; rw [e])

theorem ops_ok {x : BitVec 32} : ∀ {s : State} (l : List Op), Ctx x s → (∀ op ∈ l, opValid op = true) →
    WP isa (.block (ops l)) s fun s' => Keep s s' ∧ Frame [sub x 288 640] s.mem s'.mem ∧
      ∀ q, isSlot q = true → F s'.mem x q = run l (F s.mem x) q
  | _, [], _, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ _ => rfl⟩
  | s, op :: l, hc, hv => by
    rw [ops, List.flatMap_cons]
    refine WP.block_append (WP.mono (op_ok hc op (hv op List.mem_cons_self)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
    refine WP.mono (ops_ok l (k₁.ctx hc) fun o ho => hv o (List.mem_cons_of_mem _ ho))
      fun s₂ ⟨k₂, f₂, e₂⟩ => ⟨k₁.trans k₂, f₁.trans f₂, fun q hq => ?_⟩
    rw [e₂ q hq, run]
    exact run_congr l (fun o ho => hv o (List.mem_cons_of_mem _ ho)) e₁ q hq

end VG.Proof.X25519.X86
