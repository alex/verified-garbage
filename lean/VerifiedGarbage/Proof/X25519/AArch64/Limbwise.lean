import VerifiedGarbage.Proof.X25519.AArch64.Ops

/-!
# X25519 on AArch64: the operations limb by limb

`add`, `sub`, `copy`, `cswap` and `mulSmall`: the first four compute each limb
of their result from the same limb of their operands, loading them before
storing it, so their result may be one of their operands.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64

/-- The offsets `off` and `o` are of the same element, or of disjoint ones. -/
def Alias (o off : Nat) : Prop := o = off ∨ o + 120 ≤ off ∨ off + 120 ≤ o

instance (o off : Nat) : Decidable (Alias o off) := by unfold Alias; infer_instance

theorem Alias.ne {o a : Nat} (h : Alias o a) {i j : Nat} (hi : i < 15) (hj : j < i) :
    a + 8 * i ≠ o + 8 * j := by
  rcases h with rfl | h | h <;> omega

/-- A block that computes each limb of the element at `o` from words it reads
(`reads i`, none a limb of `o` already written), and stores it. -/
theorem limbwise_ok {b : Addr} {o : Nat} (ho : Slot o) (body : Nat → List Instr) (W : List Reg)
    (hW : Reg.x3 ∉ W) (val : Nat → Mem → Nat) (reads : Nat → List Nat) (I : State → Prop)
    (hI : ∀ s s', I s → Kp W s s' → I s')
    (hstep : ∀ i < 15, ∀ s : State, Sc b s → I s → WP isa (.block (body i)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = val i s.mem ∧ s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧
        Kp W s s')
    (hval : ∀ i < 15, ∀ m m' : Mem, (∀ off ∈ reads i, wd m' b off = wd m b off) → val i m' = val i m)
    (hreads : ∀ i < 15, ∀ off ∈ reads i, Off off ∧ ∀ j < i, off ≠ o + 8 * j) :
    ∀ n ≤ 15, ∀ s : State, Sc b s → I s → WP isa (.block ((List.range n).flatMap body)) s fun s' =>
      (∀ k < n, wd s'.mem b (o + 8 * k) = val k s.mem) ∧
      (∀ off, Off off → (∀ j < n, off ≠ o + 8 * j) → wd s'.mem b off = wd s.mem b off) ∧
      Frame [slotR b o] s.mem s'.mem ∧ Kp W s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, hIs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (limbwise_ok ho body W hW val reads I hI hstep hval hreads n (by omega)
      s hs hIs) fun s₁ ⟨e₁, u₁, f₁, k₁⟩ => ?_)
    refine WP.mono (hstep n (by omega) s₁ (hs.of_kp k₁ hW) (hI _ _ hIs k₁)) fun s₂ ⟨x, hx, m₂, k₂⟩ => ⟨fun k hk => ?_,
      fun off hoff hj => ?_, ?_, (k₁.trans k₂).sub (List.append_subset.mpr ⟨List.Subset.refl _,
        List.Subset.refl _⟩)⟩
    · rw [m₂, wd_writeW _ _ _ (ho.off (by omega)) (ho.off (by omega))]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_left rfl, hx]
        exact hval k (by omega) _ _ fun off hoff =>
          u₁ off (hreads k (by omega) off hoff).1 (hreads k (by omega) off hoff).2
      · rw [ite_eq_right (by omega)]; exact e₁ k (by omega)
    · rw [m₂, wd_writeW _ _ _ (ho.off (by omega)) hoff, ite_eq_right (hj n (by omega))]
      exact u₁ off hoff fun j hjn => hj j (by omega)
    · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (slot_contains b ho (by omega))

/-- The whole element. -/
theorem limbwise_all {b : Addr} {o : Nat} (ho : Slot o) (body : Nat → List Instr) (W : List Reg)
    (hW : Reg.x3 ∉ W) (val : Nat → Mem → Nat) (reads : Nat → List Nat) (I : State → Prop)
    (hI : ∀ s s', I s → Kp W s s' → I s')
    (hstep : ∀ i < 15, ∀ s : State, Sc b s → I s → WP isa (.block (body i)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = val i s.mem ∧ s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧
        Kp W s s')
    (hval : ∀ i < 15, ∀ m m' : Mem, (∀ off ∈ reads i, wd m' b off = wd m b off) → val i m' = val i m)
    (hreads : ∀ i < 15, ∀ off ∈ reads i, Off off ∧ ∀ j < i, off ≠ o + 8 * j) {s : State} (hs : Sc b s)
    (hIs : I s) :
    WP isa (.block ((List.range 15).flatMap body)) s fun s' =>
      limbs s'.mem b o = (fun k => if k < 15 then val k s.mem else 0) ∧
      Frame [slotR b o] s.mem s'.mem ∧ Kp W s s' :=
  WP.mono (limbwise_ok ho body W hW val reads I hI hstep hval hreads 15 (by decide) s hs hIs)
    fun _ ⟨e, _, f, k⟩ => ⟨funext fun i => by
      simp only [limbs]; split
      · rename_i hi; exact e i hi
      · rfl, f, k⟩

/-! ## Sums -/

/-- One limb of `add`. -/
theorem addStep_ok {b : Addr} {s : State} (hs : Sc b s) {o a c i : Nat} (ho : Off (o + 8 * i))
    (ha : Off (a + 8 * i)) (hc : Off (c + 8 * i)) :
    WP isa (.block [ld .x17 (a + 8 * i), ld .x19 (c + 8 * i), .add .x .x17 .x17 .x19, st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = (wd s.mem b (a + 8 * i) + wd s.mem b (c + 8 * i)) % 2 ^ 64 ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ Kp [.x17, .x19] s s' := by
  have hs1 := sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have hs2 := sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64) hs1 (show Reg.x19 ≠ .x3 by decide)
  have hs3 := sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64 + s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64)
    hs2 (show Reg.x17 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ld hs _ ha, runStep_some, exec_ld hs1 _ hc, mem_wx, exec_add_x,
    gpr_wx_self, gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide)]
  rw [exec_st hs3 _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', mem_wx, gpr_wx_self]
  refine ⟨_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [BitVec.toNat_add, wd_def, wd_def]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show (State.write _ _ _ _).gpr r = _
    rw [gpr_wx_ne _ _ hr.1, gpr_wx_ne _ _ hr.2, gpr_wx_ne _ _ hr.1]

theorem val_congr2 {b : Addr} {m m' : Mem} {p q : Nat} (h : ∀ off ∈ [p, q], wd m' b off = wd m b off) :
    wd m' b p = wd m b p ∧ wd m' b q = wd m b q :=
  ⟨h p (by simp), h q (by simp)⟩

theorem reads2 {o a c : Nat} (ha : Slot a) (hc : Slot c) (hoa : Alias o a) (hoc : Alias o c) :
    ∀ i < 15, ∀ off ∈ [a + 8 * i, c + 8 * i], Off off ∧ ∀ j < i, off ≠ o + 8 * j := by
  intro i hi off hoff
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
  rcases hoff with rfl | rfl
  · exact ⟨ha.off hi, fun j hj => hoa.ne hi hj⟩
  · exact ⟨hc.off hi, fun j hj => hoc.ne hi hj⟩

/-- `[o] = [a] + [c]`. -/
theorem add_ok {b : Addr} {s : State} (hs : Sc b s) {o a c : Nat} (ho : Slot o) (ha : Slot a)
    (hc : Slot c) (hoa : Alias o a) (hoc : Alias o c) :
    WP isa (.block (add o a c)) s fun s' =>
      limbs s'.mem b o = addF (limbs s.mem b a) (limbs s.mem b c) ∧ Frame [slotR b o] s.mem s'.mem ∧
        Kp [.x17, .x19] s s' := by
  refine WP.mono (limbwise_all ho _ [.x17, .x19] (by decide)
    (fun i m => (wd m b (a + 8 * i) + wd m b (c + 8 * i)) % 2 ^ 64) (fun i => [a + 8 * i, c + 8 * i])
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun i hi s hs _ => addStep_ok hs (ho.off hi) (ha.off hi) (hc.off hi))
    (fun i _ m m' h => by rw [(val_congr2 h).1, (val_congr2 h).2]) (reads2 ha hc hoa hoc) hs trivial)
    fun s' ⟨e, f, k⟩ => ⟨?_, f, k⟩
  rw [e]
  funext i
  simp only [addF, limbs]
  split <;> rfl

/-! ## Differences -/

/-- One limb of `sub`, with the limb `P` of `16 p` in `preg i`. -/
theorem subStep_ok {b : Addr} {s : State} (hs : Sc b s) {o a c i : Nat} (ho : Off (o + 8 * i))
    (ha : Off (a + 8 * i)) (hc : Off (c + 8 * i)) {P : Nat} (hP : v s (preg i) = P) :
    WP isa (.block [ld .x17 (a + 8 * i), ld .x19 (c + 8 * i), .add .x .x17 .x17 (preg i),
        .sub .x .x17 .x17 .x19, st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = subL (wd s.mem b (a + 8 * i)) P (wd s.mem b (c + 8 * i)) ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ Kp [.x17, .x19] s s' := by
  have hp : preg i ≠ .x17 ∧ preg i ≠ .x19 ∧ preg i ≠ .x3 := by
    simp only [preg]; split <;> decide
  have hs1 := sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have hs2 := sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64) hs1 (show Reg.x19 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ld hs _ ha, runStep_some, exec_ld hs1 _ hc, mem_wx, exec_add_x,
    exec_sub_x, gpr_wx_self, gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), gpr_wx_ne _ _ hp.1,
    gpr_wx_ne _ _ hp.2.1]
  rw [exec_st (sc_wx _ _ (sc_wx _ _ hs2 (by decide)) (by decide)) _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', mem_wx, gpr_wx_self]
  refine ⟨_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [BitVec.toNat_sub, BitVec.toNat_add, gpr_wx_ne _ _ (show Reg.x19 ≠ .x17 by decide),
      gpr_wx_self, wd_def, wd_def, ← hP, v, subL]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show (State.write _ _ _ _).gpr r = _
    rw [gpr_wx_ne _ _ hr.1, gpr_wx_ne _ _ hr.1, gpr_wx_ne _ _ hr.2, gpr_wx_ne _ _ hr.1]

theorem const16p_ok (s : State) :
    WP isa (.block const16p) s fun s' => v s' .x20 = p16 0 ∧ v s' .x21 = p16 1 ∧
      Kp [.x20, .x21] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [const16p, runBlock_cons, exec_movz, runStep_some, exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', v, gpr_wx_self, gpr_wx_ne _ _ (show Reg.x20 ≠ .x21 by decide)]
  exact ⟨by decide, by decide,
    ((((kp_wx s _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩

theorem preg_p16 {s : State} (h0 : v s .x20 = p16 0) (h1 : v s .x21 = p16 1) (i : Nat) :
    v s (preg i) = p16 i := by
  simp only [preg, p16]; split
  · rename_i h; subst h; exact h0
  · rename_i h; rw [h1]; rfl

/-- `[o] = [a] + 16 p - [c]`. -/
theorem sub_ok {b : Addr} {s : State} (hs : Sc b s) {o a c : Nat} (ho : Slot o) (ha : Slot a)
    (hc : Slot c) (hoa : Alias o a) (hoc : Alias o c) :
    WP isa (.block (sub o a c)) s fun s' =>
      limbs s'.mem b o = subF (limbs s.mem b a) (limbs s.mem b c) ∧ Frame [slotR b o] s.mem s'.mem ∧
        Kp [.x20, .x21, .x17, .x19] s s' := by
  rw [sub]
  refine WP.block_append (WP.mono (const16p_ok s) fun s₁ ⟨e0, e1, k₁, m₁⟩ => ?_)
  refine WP.mono (limbwise_all ho _ [.x17, .x19] (by decide)
    (fun i m => subL (wd m b (a + 8 * i)) (p16 i) (wd m b (c + 8 * i))) (fun i => [a + 8 * i, c + 8 * i])
    (fun s => v s .x20 = p16 0 ∧ v s .x21 = p16 1)
    (fun s s' h k => ⟨by rw [v, k.gpr _ (by decide)]; exact h.1, by rw [v, k.gpr _ (by decide)]; exact h.2⟩)
    (fun i hi s hs hI => subStep_ok hs (ho.off hi) (ha.off hi) (hc.off hi) (preg_p16 hI.1 hI.2 i))
    (fun i _ m m' h => by rw [(val_congr2 h).1, (val_congr2 h).2]) (reads2 ha hc hoa hoc)
    (hs.of_kp k₁ (by decide)) ⟨e0, e1⟩)
    fun s' ⟨e, f, k⟩ => ⟨?_, by rw [← m₁]; exact f, k₁.trans k⟩
  rw [e, m₁]
  funext i
  simp only [subF, limbs]
  split <;> rfl

/-! ## Copies -/

theorem copyStep_ok {b : Addr} {s : State} (hs : Sc b s) {o a i : Nat} (ho : Off (o + 8 * i))
    (ha : Off (a + 8 * i)) :
    WP isa (.block [ld .x17 (a + 8 * i), st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = wd s.mem b (a + 8 * i) ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ Kp [.x17] s s' := by
  have hs1 := sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ld hs _ ha, runStep_some]
  rw [exec_st hs1 _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', mem_wx, gpr_wx_self]
  exact ⟨_, rfl, rfl, ⟨fun r hr => gpr_wx_ne _ _ (by simpa using hr), rfl, rfl⟩⟩

/-- `[o] = [a]`. -/
theorem copy_ok {b : Addr} {s : State} (hs : Sc b s) {o a : Nat} (ho : Slot o) (ha : Slot a)
    (hoa : Alias o a) :
    WP isa (.block (copy o a)) s fun s' =>
      limbs s'.mem b o = limbs s.mem b a ∧ Frame [slotR b o] s.mem s'.mem ∧ Kp [.x17] s s' := by
  refine WP.mono (limbwise_all ho _ [.x17] (by decide) (fun i m => wd m b (a + 8 * i)) (fun i => [a + 8 * i])
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun i hi s hs _ => copyStep_ok hs (ho.off hi) (ha.off hi))
    (fun i _ m m' h => h _ (by simp)) (fun i hi off hoff => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      subst hoff; exact ⟨ha.off hi, fun j hj => hoa.ne hi hj⟩) hs trivial)
    fun s' ⟨e, f, k⟩ => ⟨?_, f, k⟩
  rw [e]
  funext i
  simp only [limbs]

/-! ## Conditional swaps -/

/-- `x` if the mask `m` is zero, `y` if it is all ones. -/
def csel (m x y : BitVec 64) : BitVec 64 := x ^^^ ((x ^^^ y) &&& m)

theorem csel_zero (x y : BitVec 64) : csel 0 x y = x := by
  rw [csel, show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]

theorem csel_ones (x y : BitVec 64) : csel (BitVec.allOnes 64) x y = y := by
  rw [csel, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The mask of `swap`: all ones if `sw`. -/
def maskB (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem csel_mask (sw : Bool) (x y : BitVec 64) : csel (maskB sw) x y = if sw then y else x := by
  cases sw
  · exact csel_zero x y
  · exact csel_ones x y

theorem cswapStep_ok {b : Addr} {s : State} (hs : Sc b s) {x y i : Nat} (hx : Off (x + 8 * i))
    (hy : Off (y + 8 * i)) :
    WP isa (.block [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)]) s fun s' =>
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (x + 8 * i))
          (csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64))).writeW (b + BitVec.ofNat 64 (y + 8 * i))
          (csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)) ∧
        Kp [.x17, .x19, .x20] s s' := by
  have hs1 := sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have h1 : WP isa (.block [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
      .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20]) s
      fun s₁ => s₁.gpr .x17 = csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64) ∧
        s₁.gpr .x19 = csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64) ∧
        Kp [.x17, .x19, .x20] s s₁ ∧ s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_ld hs _ hx, runStep_some, exec_ld hs1 _ hy, mem_wx, exec_eor_x,
      exec_and_x, runBlock_nil, Option.some.injEq, exists_eq_left', gpr_wx_self,
      gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), gpr_wx_ne _ _ (show Reg.x19 ≠ .x17 by decide),
      gpr_wx_ne _ _ (show Reg.x17 ≠ .x20 by decide), gpr_wx_ne _ _ (show Reg.x19 ≠ .x20 by decide),
      gpr_wx_ne _ _ (show Reg.x20 ≠ .x17 by decide),
      gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide), gpr_wx_ne _ _ (show Reg.x22 ≠ .x19 by decide),
      gpr_wx_ne _ _ (show Reg.x22 ≠ .x20 by decide)]
    refine ⟨rfl, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    · simp only [csel]
      generalize s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64 = p
      generalize s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64 = q
      generalize s.gpr Reg.x22 = m
      rw [BitVec.xor_comm q p]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [gpr_wx_ne _ _ hr.2.1, gpr_wx_ne _ _ hr.1, gpr_wx_ne _ _ hr.2.2, gpr_wx_ne _ _ hr.2.2,
        gpr_wx_ne _ _ hr.2.1, gpr_wx_ne _ _ hr.1]
  rw [show [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)] =
      ([ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20] : List Instr) ++
        ([st .x17 (x + 8 * i), st .x19 (y + 8 * i)] : List Instr) from rfl]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e17, e19, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  apply WP.of_runBlock
  rw [runBlock_cons, exec_st hs₁ _ hx, runStep_some, runBlock_cons, exec_st (hs₁.mem _) _ hy,
    runStep_some, runBlock_nil]
  exact ⟨_, rfl, by rw [e17, e19, m₁], ⟨k₁.gpr, k₁.rd, k₁.wr⟩⟩

/-- The first `n` limbs of the swap of the elements at `x` and `y` by the mask `x22`. -/
theorem cswapN_ok {b : Addr} {x y : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 120 ≤ y ∨ y + 120 ≤ x) :
    ∀ n ≤ 15, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).flatMap fun i =>
      [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)])) s fun s' =>
      (∀ k < n, wd s'.mem b (x + 8 * k) = (csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64)
          (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64)).toNat ∧
        wd s'.mem b (y + 8 * k) = (csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64)
          (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64)).toNat) ∧
      (∀ off, Off off → (∀ j < n, off ≠ x + 8 * j ∧ off ≠ y + 8 * j) → wd s'.mem b off = wd s.mem b off) ∧
      Frame [slotR b x, slotR b y] s.mem s'.mem ∧ Kp [.x17, .x19, .x20] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (cswapN_ok hx hy hxy n (by omega) s hs) fun s₁ ⟨e₁, u₁, f₁, k₁⟩ => ?_)
    have hxn := hx.off (i := n) (by omega)
    have hyn := hy.off (i := n) (by omega)
    refine WP.mono (cswapStep_ok (hs.of_kp k₁ (by decide)) hxn hyn) fun s₂ ⟨m₂, k₂⟩ =>
      ⟨fun k hk => ?_, fun off hoff hj => ?_, ?_, (k₁.trans k₂).sub (List.append_subset.mpr
        ⟨List.Subset.refl _, List.Subset.refl _⟩)⟩
    · have g22 : s₁.gpr .x22 = s.gpr .x22 := k₁.gpr _ (by decide)
      have rx : s₁.mem.readW (b + BitVec.ofNat 64 (x + 8 * n)) 64 = s.mem.readW (b + BitVec.ofNat 64 (x + 8 * n)) 64 :=
        BitVec.eq_of_toNat_eq (u₁ _ hxn fun j hj => ⟨by omega, by omega⟩)
      have ry : s₁.mem.readW (b + BitVec.ofNat 64 (y + 8 * n)) 64 = s.mem.readW (b + BitVec.ofNat 64 (y + 8 * n)) 64 :=
        BitVec.eq_of_toNat_eq (u₁ _ hyn fun j hj => ⟨by omega, by omega⟩)
      rw [m₂, wd_writeW _ _ _ hyn (hx.off (by omega)), wd_writeW _ _ _ hxn (hx.off (by omega)),
        wd_writeW _ _ _ hyn (hy.off (by omega)), wd_writeW _ _ _ hxn (hy.off (by omega))]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl, g22, rx, ry]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · rw [m₂, wd_writeW _ _ _ hyn hoff, wd_writeW _ _ _ hxn hoff, ite_eq_right (hj n (by omega)).2,
        ite_eq_right (hj n (by omega)).1]
      exact u₁ off hoff fun j hjn => hj j (by omega)
    · rw [m₂]
      exact (f₁.writeW List.mem_cons_self _ (slot_contains b hx (by omega))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (slot_contains b hy (by omega))

/-- Swaps the elements at `x` and `y` if `sw` (the mask `x22` of `sw`). -/
theorem cswap_ok {b : Addr} {s : State} (hs : Sc b s) {x y : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 120 ≤ y ∨ y + 120 ≤ x) {sw : Bool} (hm : s.gpr .x22 = maskB sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      limbs s'.mem b x = (if sw then limbs s.mem b y else limbs s.mem b x) ∧
      limbs s'.mem b y = (if sw then limbs s.mem b x else limbs s.mem b y) ∧
      Frame [slotR b x, slotR b y] s.mem s'.mem ∧ Kp [.x17, .x19, .x20] s s' :=
  WP.mono (cswapN_ok hx hy hxy 15 (by decide) s hs) fun s' ⟨e, _, f, k⟩ => ⟨funext fun i => by
    simp only [limbs]
    split
    · rename_i hi
      rw [(e i hi).1, hm, csel_mask]
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, limbs, hi, wd_def]
    · rename_i hi
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, limbs, hi], funext fun i => by
    simp only [limbs]
    split
    · rename_i hi
      rw [(e i hi).2, hm, csel_mask]
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, limbs, hi, wd_def]
    · rename_i hi
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, limbs, hi], f, k⟩

/-! ## Multiplication by `a24` -/

theorem scaleStep_ok {b : Addr} {s : State} (hs : Sc b s) {a k : Nat} (ha : Off (a + 8 * k)) (hk : k < 15) :
    WP isa (.block [ld .x17 (a + 8 * k), .mul .x (dreg k) .x17 .x20]) s fun s' =>
      v s' (dreg k) = wd s.mem b (a + 8 * k) * v s .x20 % 2 ^ 64 ∧ Kp [.x17, dreg k] s s' ∧
        s'.mem = s.mem := by
  obtain ⟨d17, -, d20, -⟩ := dreg_facts k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ld hs _ ha, runStep_some, exec_mul_x, runBlock_nil, Option.some.injEq,
    exists_eq_left', mem_wx, v, gpr_wx_self, gpr_wx_ne _ _ (show Reg.x20 ≠ .x17 by decide)]
  refine ⟨by rw [BitVec.toNat_mul, wd_def], ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [gpr_wx_ne _ _ hr.2, gpr_wx_ne _ _ hr.1]

theorem scaleN_ok {b : Addr} {a : Nat} (ha : Slot a) :
    ∀ n ≤ 15, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).flatMap fun k => [ld .x17 (a + 8 * k), .mul .x (dreg k) .x17 .x20])) s
      fun s' => (∀ k < n, v s' (dreg k) = limbs s.mem b a k * v s .x20 % 2 ^ 64) ∧ Kp (DR ++ ([.x17] : List Reg)) s s' ∧
        s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scaleN_ok ha n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.mono (scaleStep_ok (hs.of_kp k₁ (by decide)) (ha.off (i := n) (by omega)) (by omega))
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨fun k hk => ?_, (k₁.trans k₂).sub (List.append_subset.mpr
        ⟨List.Subset.refl _, ?_⟩), m₂.trans m₁⟩
    · have h20 : s₁.gpr .x20 = s.gpr .x20 := k₁.gpr _ (by decide)
      by_cases hkn : k = n
      · subst hkn
        rw [e₂, m₁, v, h20]
        simp only [limbs, show k < 15 by omega, ite_true]
      · obtain ⟨d17, -⟩ := dreg_facts k (by omega)
        have hne := dreg_ne (j := k) (k := n) (by omega) (by omega) hkn
        rw [v, k₂.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨d17, hne⟩)]
        exact e₁ k (by omega)
    · have := dreg_mem n (by omega)
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, this]

theorem constA24_ok (s : State) :
    WP isa (.block constA24) s fun s' => v s' .x20 = 121665 ∧ Kp [.x20] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [constA24, runBlock_cons, exec_movz, runStep_some, exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', v, gpr_wx_self]
  exact ⟨by decide, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩

/-- `[o] = a24 · [a]`. -/
theorem mulSmall_ok {b : Addr} {s : State} (hs : Sc b s) {o a : Nat} (ho : Slot o) (ha : Slot a) :
    WP isa (.block (mulSmall o a)) s fun s' =>
      limbs s'.mem b o = mulSmallF (limbs s.mem b a) ∧ Frame [slotR b o] s.mem s'.mem ∧
        Kp fieldRegs s s' := by
  rw [mulSmall, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (const19_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (constA24_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := (hs.of_kp k₁ (by decide)).of_kp k₂ (by decide)
  refine WP.block_append (WP.mono (scaleN_ok ha 15 (by decide) s₂ hs₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have h19₃ : s₃.gpr .x21 = 19 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), e₁]
  refine WP.block_append (WP.mono (carry_ok h19₃) fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine WP.mono (store_ok ((hs₂.of_kp k₃ (by decide)).of_kp k₄ (by decide)) ho) fun s₅ ⟨e₅, f₅, k₅⟩ =>
    ⟨?_, ?_, ?_⟩
  · rw [e₅, e₄, mulSmallF]
    refine congrArg carryF (funext fun k => ?_)
    simp only [regs, scaleF]
    split
    · rename_i hk; rw [e₃ k hk, e₂, m₂, m₁]
    · rfl
  · rw [← m₁, ← m₂, ← m₃, ← m₄]; exact f₅
  · exact (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅)))).sub (List.append_subset.mpr ⟨by decide,
      List.append_subset.mpr ⟨by decide, List.append_subset.mpr ⟨List.subset_append_left _ _, by simp⟩⟩⟩)

end VG.Proof.X25519.AArch64
