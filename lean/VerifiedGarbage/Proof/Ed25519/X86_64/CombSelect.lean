import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep

/-! Merged from `Proof.Ed25519.X86_64.CombConstants`. -/
section
/-!
# The comb's tables represent `[k 256^j]B`, and `combG` represents `[G]B`

Each entry is turned back into affine `(x, y)` (`uncache`, which the kernel
checks inverts the caching) and `checkTables` walks the tables once: within
table `j`, each entry is the previous one plus the first, with the
specification's addition, compared projectively; the first entry of table `j +
1` is `[256]` of table `j`'s, with the specification's `pointMul`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `1/2`. -/
def half : Fe := ⟨(Spec.X25519.P + 1) / 2, by decide⟩

/-- The affine `(x, y)` of a cached entry `[y - x, y + x, 2dxy]` with `Z = 1`. -/
def uncache (e : Fe × Fe × Fe) : Fe × Fe := ((e.2.1 - e.1) * half, (e.2.1 + e.1) * half)

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (affPt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hrest⟩ := hc
    have hq : Rep (affPt q) a := by
      refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
        (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
      · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hx]
      · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hy]
    cases i with
    | zero => simpa using hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ]
      convert this using 1
      rw [succ_nsmul]; abel

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 256 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (affPt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((256 ^ j) • c)) := by
  induction rows generalizing b c j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons row rows ih =>
    simp only [checkTables, Bool.and_eq_true] at hc
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk ⊢
      have := checkRow_ok b b c c hb hb row hc.1 k hk
      rw [pow_zero, one_nsmul, succ_nsmul]
      exact this
    | succ j =>
      rw [List.getD_cons_succ] at hk ⊢
      have := ih (pointMul 256 b) ((256 : Nat) • c) (pointMul_rep 256 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check :
    checkTables basePoint (combTable.map (·.map uncache)) = true := by decide +kernel

/-- The caching of `affPt (uncache e)`. -/
private def recache (e : Fe × Fe × Fe) : Fe × Fe × Fe :=
  ((uncache e).2 - (uncache e).1, (uncache e).2 + (uncache e).1,
    (uncache e).1 * (uncache e).2 * 2 * d)

private theorem tables_cached :
    combTable.all (fun row => row.all fun e => decide (recache e = e)) = true := by decide +kernel

private theorem tables_length :
    combTable.length = 32 ∧ combTable.all (fun row => row.length == 8) = true := by decide +kernel

private theorem getD_map' {α β : Type} (l : List α) (f : α → β) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

private theorem uncache_default : uncache (1, 1, 0) = (0, 1) := by decide

theorem combCached_ok (j k : Nat) (hj : j < 32) (hk : k < 9) :
    ∃ q, combCached j k = cache q ∧ Rep q ((k * 256 ^ j) • baseAff) := by
  cases k with
  | zero =>
    refine ⟨identity, ?_, ?_⟩
    · simp only [combCached, ↓reduceIte]; decide +kernel
    · rw [Nat.zero_mul, zero_smul]; exact identity_rep
  | succ k =>
    have hrow : (combTable.getD j []) ∈ combTable := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (combTable.getD j []).length = 8 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hmem : (combTable.getD j []).getD k (1, 1, 0) ∈ combTable.getD j [] := by
      have hk' : k < (combTable.getD j []).length := by rw [hlen]; omega
      rw [List.getD_eq_getElem?_getD (l := combTable.getD j []), List.getElem?_eq_getElem hk']
      exact List.getElem_mem _
    have hre := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp tables_cached _ hrow) _ hmem)
    refine ⟨affPt (uncache ((combTable.getD j []).getD k (1, 1, 0))), ?_, ?_⟩
    · simp only [combCached, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      generalize (combTable.getD j []).getD k (1, 1, 0) = e at hre
      obtain ⟨a, b, c⟩ := e
      simp only [recache, Prod.mk.injEq] at hre
      simp only [cache, affPt, Point.mk.injEq]
      exact ⟨hre.1.symm, hre.2.1.symm, hre.2.2.symm, rfl⟩
    · have hgj : (combTable.map (·.map uncache)).getD j [] = (combTable.getD j []).map uncache := by
        rw [show ([] : List (Fe × Fe)) = ([] : List (Fe × Fe × Fe)).map uncache from rfl, getD_map']
      have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
        (by rw [List.length_map, tables_length.1]; exact hj) k
        (by rw [hgj, List.length_map, hlen]; omega)
      rw [hgj, ← uncache_default, getD_map', smul_smul] at hr
      exact hr

/-- The constant the comb's digits are offset by: `8 Σ_{j < 32} 256^j`. -/
def combGVal : Nat := 8 * ((256 ^ 32 - 1) / 255)

private def combGCheck (p : Point) : Bool := combG.X * p.Z == p.X && combG.Y * p.Z == p.Y && p.Z != 0

private theorem combG_check : combGCheck (pointMul combGVal basePoint) = true := by decide +kernel

theorem combG_ok : Rep combG (combGVal • baseAff) := by
  have hp := pointMul_rep combGVal basePoint_rep
  have hc := combG_check
  simp only [combGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ combG.X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ combG.Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ (combGAff.1 * combGAff.2) * toZ 1 = toZ combGAff.1 * toZ combGAff.2
    rw [toZ_mul, toZ_one, mul_one]

theorem combGCached_eq : combGCached = cache combG := by decide +kernel

end VG.Proof.Ed25519.X86_64
end

/-!
# The comb's constant-time selection

`combMask k` stores all ones exactly when the digit in `rax` is `k`, and zero
otherwise; `selectField` then ORs every candidate's words, each ANDed with its
mask, so only the digit's candidate survives.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The mask of candidate `k`, for the digit `d`. -/
def maskVal (d k : Nat) : BitVec 64 := if d = k then BitVec.allOnes 64 else 0

private theorem mask_fact : ∀ d < 16, ∀ k < 16,
    ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64) - (1 : BitVec 32).signExtend 64) -
      ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64) - (1 : BitVec 32).signExtend 64) -
      (BitVec.ofBool (decide ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64).toNat <
        ((1 : BitVec 32).signExtend 64).toNat))).setWidth 64 = maskVal d k := by
  decide +kernel

theorem combMask_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) (k : Nat) (hk : k < 16) :
    WP isa (.block (combMask k)) s fun t =>
      t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base (combMasks + 8 * k) 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base (combMasks + 8 * k)) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combMasks]; omega) (by simp only [combMasks]; omega)⟩
  apply WP.of_runBlock
  simp only [combMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, trivial, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact mask_fact d hd k hk
  · simp only [hr, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by simp only [combMasks]; omega)

theorem combMaskPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) (n : Nat) (hn : n ≤ 16) :
    WP isa (.block ((List.range n).flatMap combMask)) s fun t =>
      (∀ k < n, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combMasks 128 s.mem t.mem := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl,
      Outside.refl _ _ _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tg, tr, tw, tm⟩ => ?_
    have ht : Scratch t base := ⟨(tg _ (by decide)).trans hs.rdi, tw ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (combMask_ok ht hd ((tg _ (by decide)).trans hax) n (by omega))
      fun u ⟨uv, ug, ur, uw, um⟩ => ?_
    refine ⟨fun k hk => ?_, fun r hr => (ug r hr).trans (tg r hr), ur.trans tr, uw.trans tw,
      tm.trans (um.mono (by simp only [combMasks]; omega) (by simp only [combMasks]; omega))⟩
    by_cases h : k < n
    · exact (um.word (d := combMasks + 8 * k) (Or.inl (by omega))
        (by simp only [combMasks]; omega)).trans (tv k h)
    · obtain rfl : k = n := by omega
      exact uv

theorem combMaskAll_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) :
    WP isa (.block combMaskAll) s fun t =>
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combMasks 128 s.mem t.mem :=
  combMaskPrefix_ok hs hd hax 9 (by decide)

/-! ## Selection -/

theorem selectCand_ok {s : State} {base : Addr} (hs : Scratch s base) (v : Spec.X25519.Fe) (k : Nat)
    (hk : k < 16) {m : BitVec 64} (hm : s.mem.readW (off base (combMasks + 8 * k)) 64 = m) :
    WP isa (.block ((List.range 4).flatMap fun w => selectWord v k w)) s fun t =>
      t.gpr .r8 = s.gpr .r8 ||| (feWord v 0 &&& m) ∧ t.gpr .r9 = s.gpr .r9 ||| (feWord v 1 &&& m) ∧
      t.gpr .r10 = s.gpr .r10 ||| (feWord v 2 &&& m) ∧
      t.gpr .r11 = s.gpr .r11 ||| (feWord v 3 &&& m) ∧ Keeps [.rcx, .r8, .r9, .r10, .r11] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (combMasks + 8 * k)) 8 :=
    ⟨_, List.mem_append_right _ hs.wr,
      Offset.contains_base _ (by simp only [combMasks]; omega) (by simp only [combMasks]; omega)⟩
  rw [show ((List.range 4).flatMap fun w => selectWord v k w) =
    [.movImm64 .rcx (feWord v 0), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r8 (.reg .rcx),
      .movImm64 .rcx (feWord v 1), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r9 (.reg .rcx),
      .movImm64 .rcx (feWord v 2), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r10 (.reg .rcx),
      .movImm64 .rcx (feWord v 3), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r11 (.reg .rcx)] from rfl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, hs.rdi, hr, hm, ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
      RegUpd.wr_setReg, RegUpd.wr_arithFlags, and_self]

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp
private theorem zero_or' (x : BitVec 64) : 0 ||| x = x := by ext i; simp
private theorem zero_or_and_ones (x : BitVec 64) : 0 ||| (x &&& BitVec.allOnes 64) = x := by
  rw [BitVec.and_allOnes, zero_or']
private theorem or_zero' (x : BitVec 64) : x = x ||| 0 := by ext i; simp

theorem sel_step (d n : Nat) (x y : BitVec 64) (hy : d = n → y = x) :
    (if d < n then x else 0) ||| (y &&& maskVal d n) = if d < n + 1 then x else 0 := by
  by_cases h : d < n
  · have hne : d ≠ n := by omega
    simp only [maskVal, h, hne, ↓reduceIte, show d < n + 1 by omega]
    exact or_and_zero x y
  · by_cases he : d = n
    · subst he
      simp only [maskVal, h, ↓reduceIte, Nat.lt_add_one, hy rfl]
      exact zero_or_and_ones x
    · simp only [maskVal, h, he, ↓reduceIte, show ¬ d < n + 1 by omega]
      exact or_and_zero 0 y

/-- The candidates `k < n`, from cleared registers. -/
theorem selectCands_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat}
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) (n : Nat) (hn : n ≤ 9) :
    WP isa (.block ((List.range n).flatMap fun k => (List.range 4).flatMap fun w =>
      selectWord (vs.getD k 0) k w)) s fun t =>
      t.gpr .r8 = s.gpr .r8 ||| (if d < n then feWord (vs.getD d 0) 0 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ||| (if d < n then feWord (vs.getD d 0) 1 else 0) ∧
      t.gpr .r10 = s.gpr .r10 ||| (if d < n then feWord (vs.getD d 0) 2 else 0) ∧
      t.gpr .r11 = s.gpr .r11 ||| (if d < n then feWord (vs.getD d 0) 3 else 0) ∧
      Keeps [.rcx, .r8, .r9, .r10, .r11] s t := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨?_, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩ <;>
      simp only [Nat.not_lt_zero, ↓reduceIte] <;> exact or_zero' _
  | succ n ih =>
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t8, t9, t10, t11, kt⟩ => ?_
    have ht : Scratch t base := ⟨(kt.1 _ (by decide)).trans hs.rdi, kt.2.2.2 ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (selectCand_ok (m := maskVal d n) ht (vs.getD n 0) n (by omega)
      (by rw [kt.2.1]; exact hm n (by omega))) fun u ⟨u8, u9, u10, u11, ku⟩ => ?_
    have hy : ∀ w, d = n → feWord (vs.getD n 0) w = feWord (vs.getD d 0) w := fun _ h => by rw [h]
    refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => (ku.1 r hr).trans (kt.1 r hr), ku.2.1.trans kt.2.1,
      ku.2.2.1.trans kt.2.2.1, ku.2.2.2.trans kt.2.2.2⟩⟩
    · rw [u8, t8, BitVec.or_assoc, sel_step d n _ _ (hy 0)]
    · rw [u9, t9, BitVec.or_assoc, sel_step d n _ _ (hy 1)]
    · rw [u10, t10, BitVec.or_assoc, sel_step d n _ _ (hy 2)]
    · rw [u11, t11, BitVec.or_assoc, sel_step d n _ _ (hy 3)]

/-- `store4`, in the larger scratch. -/
theorem store4W_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (Impl.X25519.X86_64.store4 o)) s fun t =>
      t.mem = Proof.X25519.X86_64.st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [Impl.X25519.X86_64.store4, Impl.X25519.X86_64.stores, runBlock_cons, runStep_some,
    runBlock_nil, exec, Proof.X25519.X86_64.ea_sc, hs.rdi, State.store64, w o (by omega),
    w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial⟩

theorem feWord_val (v : Spec.X25519.Fe) :
    Proof.X25519.X86_64.val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (selectField vs o)) s fun t =>
      Proof.X25519.X86_64.F t.mem base o = vs.getD d 0 ∧
      (∀ r, r ∉ [Reg.rcx, .r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base o 32 s.mem t.mem := by
  rw [selectField, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Proof.X25519.X86_64.zero4_ok s) fun a ⟨a8, a9, a10, a11, ka⟩ => ?_
  have ha : Scratch a base := ⟨(ka.1 _ (by decide)).trans hs.rdi, ka.2.2.2 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (d := d) ha (by rw [ka.2.1]; exact hm) vs 9 (Nat.le_refl _))
    fun b ⟨b8, b9, b10, b11, kb⟩ => ?_
  have hb : Scratch b base := ⟨(kb.1 _ (by decide)).trans ha.rdi, kb.2.2.2 ▸ ha.wr, hs.nowrap⟩
  refine WP.mono (store4W_ok hb ho) fun t ⟨tm, tg, tr, tw⟩ => ?_
  refine ⟨?_, fun r hr => ?_, tr.trans (kb.2.2.1.trans ka.2.2.1), tw.trans (kb.2.2.2.trans ka.2.2.2),
    ?_⟩
  · rw [tm, Proof.X25519.X86_64.F, Proof.X25519.X86_64.fe_st4 _ _ (by omega), b8, b9, b10, b11, a8, a9,
      a10, a11]
    simp only [hd, ↓reduceIte, zero_or']
    rw [feWord_val, Proof.X25519.toFe_self]
  · rw [tg, kb.1 r hr, ka.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h <;> simp [h]))]
  · rw [tm, kb.2.1, ka.2.1]
    exact Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _

private theorem entries_getD (j d : Nat) (hd : d < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD d 0 = f (combCached j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
    Option.getD_some]

/-- A field selected to slot `i` (4 to 7), keeping the masks and the slots below. -/
private theorem selectSlot_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) (i : Slot) (hi : 4 ≤ i.val) (hi' : i.val < 8) :
    WP isa (.block (selectField vs (offset i))) s fun t =>
      env t.mem base i = vs.getD d 0 ∧
      (∀ i' : Slot, i' ≠ i → env t.mem base i' = env s.mem base i') ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) := by
  refine WP.mono (selectField_ok hs hd hm vs (by simp only [offset]; omega))
    fun t ⟨tv, tg, tr, tw, tm⟩ => ⟨tv, fun i' hi' => ?_, ⟨fun r hr => tg r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)), tr, tw,
      tm.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      fun k hk => (tm.word (d := combMasks + 8 * k) (Or.inr (by simp only [offset, combMasks]; omega))
        (by simp only [combMasks]; omega)).trans (hm k hk)⟩
  have hne : i'.val ≠ i.val := fun h => hi' (Fin.ext h)
  exact Outside_F tm (by simp only [offset]; omega) (by simp only [offset]; omega)

theorem combSelect_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      point (env t.mem base) 4 5 6 7 = combCached j d ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok hs hd hm _ 4 (by decide) (by decide)) fun a ⟨av, ao, ka, am⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok (hs.of_keep ka) hd am _ 5 (by decide) (by decide))
    fun b ⟨bv, bo, kb, bm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok ((hs.of_keep ka).of_keep kb) hd bm _ 6 (by decide) (by decide))
    fun c ⟨cv, co, kc, cm⟩ => ?_
  refine WP.mono (selectSlot_ok (((hs.of_keep ka).of_keep kb).of_keep kc) hd cm _ 7 (by decide)
    (by decide)) fun t ⟨tv, tO, kt, tm⟩ => ⟨?_, ((ka.trans kb).trans kc).trans kt, tm, fun i hi => ?_⟩
  · rw [entries_getD j d hd] at av bv cv tv
    simp only [point, tv, tO 6 (by decide), cv, tO 5 (by decide), co 5 (by decide), bv,
      tO 4 (by decide), co 4 (by decide), bo 4 (by decide), av]
  · have ne : ∀ (k : Nat) (h2 : k < 8), 4 ≤ k → i ≠ (⟨k, by omega⟩ : Slot) := fun k _ h1 h => by
      have := congrArg Fin.val h; simp only at this; omega
    rw [tO i (ne 7 (by decide) (by decide)), co i (ne 6 (by decide) (by decide)),
      bo i (ne 5 (by decide) (by decide)), ao i (ne 4 (by decide) (by decide))]

theorem rdxCmp_ok (s : State) (j k : Nat) (hj : j < 32) (hk : k < 32)
    (hc : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (j = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 32, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {s : State} {j : Nat}
    (hj : j ∈ ks) (hj32 : j < 32) (hc : s.gpr .rdx = BitVec.ofNat 64 j) {Q : State → Prop}
    (hq : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block (combSelect j)) s' Q) :
    WP isa (combSelectFrom ks) s Q := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    rw [combSelectFrom]
    refine WP.seq (WP.mono (rdxCmp_ok s j k hj32 (hks k (by simp)) hc)
      fun t ⟨tz, tg, tm, tr, tw⟩ => ?_)
    refine WP.ite (decide (j = k)) (by simp only [eval, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      exact hq t tg tm tr tw
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      exact ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) hj' (by rw [tg]; exact hc)
        (fun s' g m r w => hq s' (g.trans tg) (m.trans tm) (r.trans tr) (w.trans tw))

theorem combSelectAll_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) {j : Nat}
    (hj : j < 32) (hc : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (combSelectFrom (List.range 32)) s fun t =>
      point (env t.mem base) 4 5 6 7 = combCached j d ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  refine combSelectFrom_ok _ (fun k hk => List.mem_range.mp hk) (List.mem_range.mpr hj) hj hc ?_
  intro t tg tm tr tw
  have ht : Scratch t base := ⟨by rw [tg]; exact hs.rdi, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (combSelect_ok ht hd (by rw [tm]; exact hm) j) fun u ⟨uv, ku, um, ue⟩ =>
    ⟨uv, ?_, um, fun i hi => by rw [ue i hi, tm]⟩
  exact ⟨fun r hr => (ku.gpr r hr).trans (by rw [tg]), ku.rd.trans tr, ku.wr.trans tw,
    by rw [← tm]; exact ku.mem⟩

end VG.Proof.Ed25519.X86_64
