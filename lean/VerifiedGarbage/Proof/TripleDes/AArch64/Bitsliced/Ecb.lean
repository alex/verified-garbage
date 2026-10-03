import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Copy

/-!
# The function

While at least 128 blocks are left, a batch runs on the next 128 in place
(`wide_ok`); the `n mod 128` blocks left, if any, are copied into the
scratch buffer, run as a batch there, and copied back (`tail_ok`). Every
block becomes its encryption or decryption (`ecb_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le ecb_blocks)

/-- What the function may assume of the state it starts in: the schedule
readable, the `n` blocks of data and the scratch buffer writable, apart from
each other. -/
structure Env (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 384⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 1024⟩]
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

theorem Env.len {s : State} (E : Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.keyIn {s : State} (E : Env s) :
    ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  have e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

/-! ## The batches of 128 blocks -/

/-- The registers the batches change. -/
def WideRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10

/-- `m` blocks left, a multiple of 128 fewer than `n`, and at least 128. -/
structure WideInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 128 ≤ m
  le : m ≤ n
  mod : m % 128 = n % 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩] s₀.mem s.mem

structure WidePost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = BitVec.ofNat 64 (n % 128)
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - n % 128)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - n % 128, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - n % 128)⟩] s₀.mem s.mem

theorem lsr7 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 7 = BitVec.ofNat 64 (m / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ofNat_ne_zero {m : Nat} (h : m < 2 ^ 64) (h0 : m ≠ 0) : BitVec.ofNat 64 m ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this
  omega

theorem eval_nonzero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem eval_zero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem loop_ok (d : Direction) {s₀ : State} (E : Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (hs : WideInv d s₀ n m s) :
    WP isa (.loop (.seq (.block [.addImm .x .x4 .x1 0]) (.seq (batch d)
        (.block [.addImm .x .x1 .x1 1024, .subImm .x .x2 .x2 128, wholeLeft])))
      (.nonzero .x .x10)) s (WidePost d s₀ n) := by
  refine WP.loop (M := isa) (WideInv d s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hge := h.ge
  have hle := h.le
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have g := h.gpr
  have hx0 : s.gpr .x0 = S := g _ (by simp [WideRegs])
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  have dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  have room₁ : Room s₁ := Ok.of_off (off := 8 * (n - m)) dataR (by show s₁.gpr .x4 = _; rw [x4₁]) (by
    show 8 * (n - m) + 16 * 64 ≤ 8 * n; omega) (by omega)
  have st₁ : stateR s₁ = ⟨wAt D (n - m), 1024⟩ := by simp only [stateR, x4₁]
  have stSub : Region.Sub (stateR s₁) ⟨D, 8 * n⟩ := by
    rw [st₁]; exact Offset.sub_base _ (by omega)
  have S₁ : Sched s₁ := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [g₁ _ (by decide), hx0]
      show InRegions (s.rd ++ s.wr) _ 8
      rw [h.rd, h.wr]; exact E.keyIn i hi
    · rw [g₁ _ (by decide), hx0]
      exact (hn ▸ E.keyData).sub_right stSub
  apply WP.seq
  apply WP.mono (batch_ok d room₁ S₁)
  intro s₂ q
  have g₂ : ∀ r, r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x4 → s₂.gpr r = s.gpr r :=
    fun r a b c e f => (q.gpr r a b c e).trans (g₁ r f)
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 1024)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 128)
  let s₅ := s₄.write .x .x10 (s₄.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  have x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 128) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x2,
      show (BitVec.ofNat 64 128) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have x1₅ : s₅.gpr .x1 = wAt D (n - (m - 128)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  have x10₅ : s₅.gpr .x10 = BitVec.ofNat 64 ((m - 128) / 128) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, lsr7 _ (by omega)]
  have g₅ : ∀ r, WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a, b, c, e, f, i, j⟩
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, j, b, a, ite_false]
    rw [g₂ r e f i j c, g r ⟨a, b, c, e, f, i, j⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  -- the memory written so far
  have frame' : Frame [⟨D, 8 * (n - (m - 128))⟩] s₀.mem s₅.mem := by
    have f₁ : Frame [⟨D, 8 * (n - (m - 128))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
    have f₂ : Frame [⟨D, 8 * (n - (m - 128))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by rw [st₁]; exact Offset.sub_base _ (by omega)⟩
    rw [mem₅]; exact f₁.trans f₂
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s₀.gpr .x3, 1024⟩ := hn ▸ E.dataBuf
  have done' : ∀ b < n - (m - 128), blockAt s₅.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    rw [mem₅]
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [st₁]
      exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := q.out j (by omega)
      rw [x4₁, wAt_wAt] at e
      rw [e, g₁ _ (by decide), hx0]
      have hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega) (by omega)
      show blockOut (scheduleAt s₁.mem S) d (blockAt s₁.mem _) = _
      rw [show s₁.mem = s.mem from rfl, hK, hB]
  have wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  have rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  have sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  have flag := eval_nonzero s₅ .x10 x10₅ (by omega)
  by_cases hend : m - 128 < 128
  · left
    have e : m - 128 = n % 128 := by have := h.mod; omega
    refine ⟨by rw [flag]; simp; omega, by rw [x2₅, e], by rw [x1₅, e], g₅, rd₅, wr₅, sp₅,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by rw [flag]; simp; omega, m - 128, by omega,
      ⟨by omega, by omega, by have := h.mod; omega, x2₅, x1₅, g₅, rd₅, wr₅, sp₅, done', frame'⟩⟩

theorem wide_ok (d : Direction) {s : State} (E : Env s) :
    WP isa (wide d) s (WidePost d s (s.gpr .x2).toNat) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 (n / 128) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], lsr7 _ hl]
  have g₁ : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.ite _ (eval_zero s₁ .x10 x10₁ (by omega))
  · intro hz
    have hz' : n < 128 := by simp at hz; omega
    apply WP.block_nil
    have e : n % 128 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, fun r hr => g₁ r hr.2.2.2.2.2.2, rfl, rfl, rfl, fun b hb => by omega, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    have hge : 128 ≤ n := by simp at hnz; omega
    have E₁ : Env s₁ := by
      have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      have h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit⟩
    have hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    have I : WideInv d s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok d E₁ hn₁ n s₁ I)
    intro s₂ p
    have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁ r hr.2.2.2.2.2.2), p.rd, p.wr,
      p.sp, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb, h0, h1]; rfl

end VG.Proof.TripleDes.AArch64.BitslicedNeon
