import VerifiedGarbage.Proof.X448.X86.Columns

/-!
# X448 on x86 (32-bit): reducing product limbs

The upper half folds using `2^448 = 2^224 + 1` modulo the field prime.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem loadAdd_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 4096) :
    WP isa (.block [.alu .add .eax (.mem (sc d))]) s fun t =>
      t.gpr .eax = s.gpr .eax + word s.mem base d ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  have rd : readSrc s (.mem (sc d)) = some (word s.mem base d) := by
    simp only [readSrc, hs.ea (d := d) (by omega), State.load32,
      hs.read (d := d) (n := 4) (by omega), ite_true]
  refine wp_alu (Or.inl rfl) rd fun t ht _ => WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

/-- A bounded sum of words, accumulated into `eax`. -/
def addWords (ds : List Nat) : List Instr :=
  ds.flatMap fun d => [.alu .add .eax (.mem (sc d))]

theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base) {ds : List Nat}
    (hd : ∀ d ∈ ds, d + 4 ≤ 4096) :
    WP isa (.block (addWords ds)) s fun t =>
      t.gpr .eax = s.gpr .eax + (ds.map fun d => word s.mem base d).sum ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨(BitVec.add_zero _).symm, rfl, Keeps.refl _ _⟩
  | cons d ds ih =>
    change WP isa (.block (([.alu .add .eax (.mem (sc d))] : List Instr) ++ addWords ds)) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadAdd_ok hs (hd d List.mem_cons_self)) fun t ⟨tv, tm, tk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps tk (by decide)) (fun d h => hd d (List.mem_cons_of_mem _ h)))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
    rw [uv, tv, tm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc]

/-- The extra offsets folded into product limb `k`. -/
def colOffsets (k : Nat) : List Nat :=
  [ACC + 4 * (k + 28)] ++
    if k < 14 then [ACC + 4 * (k + 42)] else [ACC + 4 * (k + 14), ACC + 4 * (k + 28)]

theorem colOffsets_bound {k : Nat} (hk : k < 28) : ∀ d ∈ colOffsets k, d + 4 ≤ 4096 := by
  intro d hd
  simp only [colOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd
  · simp only [ACC]; omega
  · split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · subst d; simp only [ACC]; omega
    · rcases hd with rfl | rfl <;> simp only [ACC] <;> omega

theorem reduceCol_code (k : Nat) : reduceCol k =
    [ld .eax (ACC + 4 * k)] ++ addWords (colOffsets k) ++ [st .eax (TMP + 4 * k)] := by
  unfold reduceCol colOffsets
  split <;> rfl

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 28)
    {f : Nat → Nat} (hf : ∀ i < 56, limbs s.mem base ACC i = f i)
    (hb : ∀ i < 56, f i < radix) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * k)) (BitVec.ofNat 32 (reduced f k)) ∧
      Keeps [.eax] s t := by
  rw [reduceCol_code, List.append_assoc]
  refine load_ok hs (by simp only [ACC]; omega) fun t ht => ?_
  change WP isa (.block (addWords (colOffsets k) ++ ([st .eax (TMP + 4 * k)] : List Instr))) t _
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok (hs.of_upd ht (by decide)) (colOffsets_bound hk))
    fun u ⟨uv, um, uk⟩ => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  refine store_ok us (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    have f0 := hf k (by omega)
    have f1 := hf (k + 28) (by omega)
    have b0 := hb k (by omega)
    have b1 := hb (k + 28) (by omega)
    by_cases h : k < 14
    · have f2 := hf (k + 42) (by omega)
      have b2 := hb (k + 42) (by omega)
      simp only [colOffsets, h, ite_true, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_true]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 42)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega
    · have f2 := hf (k + 14) (by omega)
      have b2 := hb (k + 14) (by omega)
      simp only [colOffsets, h, ite_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_false]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 14) + (limbs s.mem base ACC (k + 28)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

/-- Fold all fifty-six product limbs into twenty-eight, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 56, limbs s.mem base ACC i = f i) (hb : ∀ i < 56, f i < radix) :
    WP isa (.block ((List.range 28).flatMap reduceCol)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = reduced f i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = reduced f i) ∧
    Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 56, limbs t.mem base ACC i = f i := by
      intro i hi
      change (word t.mem base (ACC + 4 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega)) (by simp only [ACC]; omega)]
      exact hf i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86
