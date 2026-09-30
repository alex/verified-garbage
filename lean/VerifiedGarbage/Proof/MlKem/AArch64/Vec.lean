import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: vectors

Untrusted: everything here is checked by Lean. What the vector code needs
(`Impl/MlKem/AArch64/Ntt.lean`, "Vectors"): a 16-byte load or store is four
32-bit words (`read16`, `write16`), the lanes of the results of the vector
instructions (`vword_*`), weakest-precondition rules for them (`wp_vop`,
`wp_ldrq`, `wp_strq`), and that code without them keeps the vector
registers (`WP.keepV`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! ## Memory -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem getLsbD_readW32 (m : Mem) (a : Addr) (k : Nat) {j : Nat} (hj : j < 32) :
    (m.readW (a + BitVec.ofNat 64 (4 * k)) 32).getLsbD j =
      (m (a + BitVec.ofNat 64 ((32 * k + j) / 8))).getLsbD ((32 * k + j) % 8) := by
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  rw [show 32 / 8 = 4 from rfl, getLsbD_read m 4 _ j (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * k + j / 8 = (32 * k + j) / 8 by omega, show j % 8 = (32 * k + j) % 8 by omega]

theorem read16 (m : Mem) (a : Addr) :
    m.read a 16 = ofVWords (m.readW (a + BitVec.ofNat 64 (4 * 0)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 1)) 32)
      (m.readW (a + BitVec.ofNat 64 (4 * 2)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 3)) 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read m 16 a i (by omega)]
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp only [h0]; rw [getLsbD_readW32 m a 0 h0]; simp
  by_cases h1 : i - 32 < 32
  · simp only [h0, h1]
    rw [getLsbD_readW32 m a 1 h1, show 32 * 1 + (i - 32) = i by omega]; simp
  by_cases h2 : i - 32 - 32 < 32
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 2 h2, show 32 * 2 + (i - 32 - 32) = i by omega]; simp
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 3 (by omega), show 32 * 3 + (i - 32 - 32 - 32) = i by omega]; simp

theorem toNat_sub_c (d : BitVec 64) (c : Nat) (hc : c < 16) :
    (d - BitVec.ofNat 64 c).toNat = if c ≤ d.toNat then d.toNat - c else 2 ^ 64 + d.toNat - c := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := d.isLt
  split <;> omega

/-- The low word of a 64-bit load. -/
theorem readW64_lo (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add, Mem.readW,
    BitVec.getLsbD_setWidth, show i < 64 by omega]
  rw [getLsbD_read m _ a i (by omega), getLsbD_read m _ a i (by omega)]

/-- The high word of a 64-bit load. -/
theorem readW64_hi (m : Mem) (a : Addr) :
    (m.readW a 64).extractLsb' 32 32 = m.readW (a + BitVec.ofNat 64 4) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW,
    BitVec.getLsbD_setWidth, show 32 + i < 64 by omega]
  rw [getLsbD_read m _ a (32 + i) (by omega), getLsbD_read m _ _ i (by omega), BitVec.add_assoc,
    ← BitVec.ofNat_add, show 4 + i / 8 = (32 + i) / 8 by omega, show i % 8 = (32 + i) % 8 by omega]

theorem getLsbD_ofVWords (w0 w1 w2 w3 : BitVec 32) {i : Nat} (hi : i < 128) :
    (ofVWords w0 w1 w2 w3).getLsbD i =
      if i < 32 then w0.getLsbD i else if i < 64 then w1.getLsbD (i - 32)
      else if i < 96 then w2.getLsbD (i - 64) else w3.getLsbD (i - 96) := by
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp [h0]
  by_cases h1 : i < 64
  · simp [h0, h1, show i - 32 < 32 by omega]
  by_cases h2 : i < 96
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega, show i - 64 < 32 by omega]
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 = i - 96 by omega]

theorem write16 (m : Mem) (a : Addr) (w0 w1 w2 w3 : BitVec 32) :
    m.write a 16 (ofVWords w0 w1 w2 w3) =
      (((m.writeW a w0).writeW (a + BitVec.ofNat 64 4) w1).writeW (a + BitVec.ofNat 64 8) w2).writeW
        (a + BitVec.ofNat 64 12) w3 := by
  funext x
  have e : ∀ c : Nat, x - (a + BitVec.ofNat 64 c) = (x - a) - BitVec.ofNat 64 c := fun c => by
    bv_omega
  simp only [Mem.writeW, Mem.write, e, show 32 / 8 = 4 from rfl]
  generalize x - a = d
  rw [toNat_sub_c d 4 (by omega), toNat_sub_c d 8 (by omega), toNat_sub_c d 12 (by omega)]
  have := d.isLt
  have ext : ∀ (k : Nat) (w : BitVec 32), k < 4 → 4 * k ≤ d.toNat → d.toNat < 4 * k + 4 →
      (∀ b < 8, w.getLsbD (8 * (d.toNat - 4 * k) + b) = (ofVWords w0 w1 w2 w3).getLsbD (8 * d.toNat + b)) →
      (ofVWords w0 w1 w2 w3).extractLsb' (8 * d.toNat) 8 =
        (w.setWidth (8 * 4)).extractLsb' (8 * (d.toNat - 4 * k)) 8 := by
    intro k w hk h1 h2 hw
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show 8 * (d.toNat - 4 * k) + b < 8 * 4 by omega]
    exact (hw b hb).symm
  have g := fun (b : Nat) (h : 8 * d.toNat + b < 128) => getLsbD_ofVWords w0 w1 w2 w3 h
  by_cases c3 : 12 ≤ d.toNat
  · by_cases c4 : d.toNat < 16
    · simp only [c3, c4, ite_true, show d.toNat - 12 < 4 by omega]
      refine ext 3 w3 (by omega) c3 (by omega) fun b hb => ?_
      rw [g b (by omega)]
      simp only [show ¬ 8 * d.toNat + b < 96 by omega, show ¬ 8 * d.toNat + b < 64 by omega,
        show ¬ 8 * d.toNat + b < 32 by omega, ite_false, show 8 * (d.toNat - 4 * 3) + b = 8 * d.toNat + b - 96 by omega]
    · simp only [c3, c4, ite_true, ite_false, show ¬ d.toNat - 12 < 4 by omega,
        show ¬ d.toNat - 8 < 4 by omega, show ¬ d.toNat - 4 < 4 by omega, show 8 ≤ d.toNat by omega,
        show 4 ≤ d.toNat by omega, show ¬ d.toNat < 4 by omega]
  by_cases c2 : 8 ≤ d.toNat
  · simp only [c3, c2, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat - 8 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega]
    refine ext 2 w2 (by omega) c2 (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 96 by omega, show ¬ 8 * d.toNat + b < 64 by omega,
      show ¬ 8 * d.toNat + b < 32 by omega, ite_false, ite_true,
      show 8 * (d.toNat - 4 * 2) + b = 8 * d.toNat + b - 64 by omega]
  by_cases c1 : 4 ≤ d.toNat
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat - 4 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by omega]
    refine ext 1 w1 (by omega) c1 (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 64 by omega, show ¬ 8 * d.toNat + b < 32 by omega, ite_false,
      ite_true, show 8 * (d.toNat - 4 * 1) + b = 8 * d.toNat + b - 32 by omega]
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 4 < 4 by omega]
    refine ext 0 w0 (by omega) (by omega) (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 32 by omega, ite_true, show 8 * (d.toNat - 4 * 0) + b = 8 * d.toNat + b by omega]


/-! ## Lanes -/

theorem vword_ofVWords (w0 w1 w2 w3 : BitVec 32) {e : Nat} (he : e < 4) :
    vword (ofVWords w0 w1 w2 w3) e = [w0, w1, w2, w3][e] := by
  ext i hi
  simp only [vword, ofVWords, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp +arith [hi]

/-- Two vectors with the same lanes are the same. -/
theorem vec_ext {x y : BitVec 128} (h : ∀ e < 4, vword x e = vword y e) : x = y := by
  ext i hi
  have := congrArg (fun w : BitVec 32 => w.getLsbD (i % 32)) (h (i / 32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show i % 32 < 32 by omega, decide_true,
    Bool.true_and, show 32 * (i / 32) + i % 32 = i by omega] at this
  simpa [BitVec.getElem_eq_testBit_toNat, BitVec.getLsbD] using this

theorem ofVWords_vword (x : BitVec 128) : ofVWords (vword x 0) (vword x 1) (vword x 2) (vword x 3) = x :=
  vec_ext fun e he => by
    rw [vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- The lanes of the result of an operation on the lanes of two vectors. -/
theorem vword_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 4) : vword (VArr.s4.map2 f x y) e = f 32 (vword x e) (vword y e) := by
  simp only [VArr.map2]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_mapWords3 (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x y z : BitVec 128)
    {e : Nat} (he : e < 4) : vword (mapWords3 f x y z) e = f (vword x e) (vword y e) (vword z e) := by
  simp only [mapWords3]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Lane lemmas: each lane of each case, bit by bit. -/
macro "lane_tac" e:ident i:ident : tactic => `(tactic| (
  (rcases (show $e = 0 ∨ $e = 1 ∨ $e = 2 ∨ $e = 3 by omega) with h | h | h | h) <;> subst h <;>
    simp +arith [List.range_succ] <;> (repeat rw [BitVec.getLsbD_append]) <;>
    simp +arith [BitVec.getLsbD_extractLsb'] <;>
    (try simp [show $i ≤ 63 by omega, show $i ≤ 31 by omega, show $i ≤ 95 by omega]) <;>
    (try intro) <;> (try omega)))

set_option linter.unusedSimpArgs false

theorem vword_trn1_d2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .trn1 .d2 x y) e = if e < 2 then vword x e else vword y (e - 2) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, vdword, ofVDwords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_trn2_d2 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .trn2 .d2 x y) e = if e < 2 then vword x (e + 2) else vword y e := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, vdword, ofVDwords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_zip1_s4 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x x) e = vword x (e / 2) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, ofVWords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_dup_d2 (g : BitVec 64) {e : Nat} (he : e < 4) :
    vword (ofVDwords g g) e = g.extractLsb' (32 * (e % 2)) 32 := by
  ext i hi
  simp only [vword, ofVDwords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_rev64s (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VRevOp.eval .rev64s x) e = vword x (if e % 2 = 0 then e + 1 else e - 1) := by
  ext i hi
  simp only [VRevOp.eval, vword, ofVBytes, vbyte, BitVec.getElem_extractLsb']
  lane_tac e i
  all_goals (repeat' split) <;> simp_all <;> (congr 1; omega)

theorem vword_uzp1_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp1 .s4 x y) e = if e < 2 then vword x (2 * e) else vword y (2 * (e - 2)) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, ofVWords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_uzp2_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .uzp2 .s4 x y) e =
      if e < 2 then vword x (2 * e + 1) else vword y (2 * (e - 2) + 1) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, ofVWords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_zip1_s4' (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip1 .s4 x y) e = if e % 2 = 0 then vword x (e / 2) else vword y (e / 2) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, ofVWords, BitVec.getElem_extractLsb']
  lane_tac e i

theorem vword_zip2_s4 (x y : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VPermOp.eval .zip2 .s4 x y) e =
      if e % 2 = 0 then vword x (2 + e / 2) else vword y (2 + e / 2) := by
  ext i hi
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword, ofVWords, BitVec.getElem_extractLsb']
  lane_tac e i

set_option linter.unusedSimpArgs true

theorem vword_dup_s4 (w : BitVec 32) {e : Nat} (he : e < 4) : vword (ofVWords w w w w) e = w := by
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- SQDMULH on lanes less than `2³¹`: `⌊a · b / 2³¹⌋`, without saturating. -/
theorem sqdmulhLane_lt {a b : BitVec 32} (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    sqdmulhLane a b = some (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 31)) := by
  have hne : ¬ (a = 0x80000000#32 ∧ b = 0x80000000#32) := fun h => by
    rw [h.1] at ha; exact absurd ha (by decide)
  simp only [sqdmulhLane, hne, ite_false, Option.some.injEq]
  rw [BitVec.toInt_eq_toNat_of_lt (by omega), BitVec.toInt_eq_toNat_of_lt (by omega),
    show (2 : Int) * a.toNat * b.toNat = ((2 * a.toNat * b.toNat : Nat) : Int) by push_cast; rfl,
    ← Int.natCast_shiftRight, BitVec.ofInt_natCast, Nat.shiftRight_eq_div_pow,
    show 2 * a.toNat * b.toNat / 2 ^ 32 = a.toNat * b.toNat / 2 ^ 31 by rw [Nat.mul_assoc]; omega]

/-! ## Instructions -/

/-- `s'` is `s` with the vector register `d` set to `x`. -/
structure VUpd (s s' : State) (d : VReg) (x : BitVec 128) : Prop where
  v : s'.v d = x
  other : ∀ r, r ≠ d → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- A vector register other than `d` is kept. -/
theorem VUpd.get {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) (r : VReg)
    (hr : r ≠ d := by decide) : s'.v r = s.v r := h.other r hr

theorem VUpd.keep {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem vupd_setV (s : State) (d : VReg) (x : BitVec 128) : VUpd s (s.setV d x) d x :=
  ⟨by simp [State.setV], fun r h => by simp [State.setV, h], rfl, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure VMem (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  v : s'.v = s.v
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vop {op : VOp} {d : VReg} {x : BitVec 128} (he : op.eval s = some (d, x))
    (k : ∀ s', VUpd s s' d x → WP isa (.block is) s' Q) : WP isa (.block (.vop op :: is)) s Q :=
  WP.cons (s' := s.setV d x) (by simp only [exec, he, Option.map_some]) (k _ (vupd_setV s d x))

theorem wp_ldrq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', VUpd s s' t (s.mem.read a 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq t n off :: is)) s Q :=
  WP.cons (s' := s.setV t (s.mem.read a 16))
    (by simp only [exec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
      Option.map_some]) (k _ (vupd_setV _ _ _))

theorem wp_strq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', VMem s s' (s.mem.write a 16 (s.v t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strq t n off :: is)) s Q :=
  WP.cons (s' := { s with mem := s.mem.write a 16 (s.v t) })
    (by simp only [exec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Whether an instruction writes a vector register. -/
def writesV : Instr → Bool
  | .vop _ | .ldrq .. => true
  | _ => false

theorem exec_v {i : Instr} (hi : writesV i = false) {s s' : State} (h : exec i s = some s') :
    s'.v = s.v := by
  cases i <;> simp only [writesV, Bool.true_eq_false] at hi <;>
    simp only [exec] at h <;>
    (try (obtain ⟨⟩ := h)) <;>
    (try split at h) <;> (try (obtain ⟨⟩ := h)) <;>
    simp_all [State.write, State.store, State.load, Option.bind_eq_some_iff] <;>
    (obtain ⟨_, _, _, rfl⟩ := h; rfl)

/-- Code that writes no vector register keeps them. -/
theorem WP.keepV : ∀ {is : List Instr} {s : State} {Q : State → Prop},
    (is.all fun i => !writesV i) = true → WP isa (.block is) s Q →
      WP isa (.block is) s fun s' => Q s' ∧ s'.v = s.v
  | [], _, _, _, h => WP.block_nil_iff.mpr ⟨WP.block_nil_iff.mp h, rfl⟩
  | _ :: _, _, _, hno, h => by
    obtain ⟨s₁, he, h₁⟩ := WP.block_cons_iff.mp h
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hno
    exact WP.block_cons_iff.mpr ⟨s₁, he, WP.mono (WP.keepV hno.2 h₁) fun _ ⟨hq, hv⟩ =>
      ⟨hq, hv.trans (exec_v hno.1 he)⟩⟩

/-- Scalar code `is`, proved with the scalar rules, keeps the vector
registers for the code after it. -/
theorem wp_scalar {is rest : List Instr} {s : State} {P Q : State → Prop}
    (hno : (is.all fun i => !writesV i) = true) (h : WP isa (.block is) s P)
    (hq : ∀ s', P s' → s'.v = s.v → WP isa (.block rest) s' Q) : WP isa (.block (is ++ rest)) s Q := by
  rw [WP.block_append_iff]
  exact WP.mono (WP.keepV hno h) fun s' ⟨p, v⟩ => hq s' p v

/-! ## Arithmetic modulo `q` -/

/-- `min(d, d - q)` in 32 bits is `d mod q`, for `d < 2q`. -/
theorem csub_nat {d : Nat} (h : d < 2 * 3329) : min d ((d + (2 ^ 32 - 3329)) % 2 ^ 32) = d % 3329 := by
  omega

private theorem barrett_sum (t : Nat) :
    (t * 2147483648 + 2147483648) * 3329 + 3329 * 2147483648 = (t * 3329 + 2 * 3329) * 2147483648 := by
  omega

/-- Barrett reduction with `M = ⌊2³¹ / q⌋ = 645083`: `t = ⌊x · M / 2³¹⌋` is at
most `x / q`, and more than `x / q - 2`. -/
theorem barrett_nat {x : Nat} (hx : x < 2147483648) :
    x * 645083 / 2147483648 * 3329 ≤ x ∧ x < x * 645083 / 2147483648 * 3329 + 2 * 3329 := by
  have h1 := Nat.div_mul_le_self (x * 645083) 2147483648
  have h2 := Nat.lt_div_mul_add (a := x * 645083) (b := 2147483648) (by decide)
  generalize x * 645083 / 2147483648 = t at h1 h2 ⊢
  constructor
  · have : t * 3329 * 2147483648 ≤ x * 2147483648 := by
      calc t * 3329 * 2147483648 = t * 2147483648 * 3329 := by rw [Nat.mul_right_comm]
        _ ≤ x * 645083 * 3329 := Nat.mul_le_mul_right _ h1
        _ ≤ x * 2147483648 := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by decide)
    exact Nat.le_of_mul_le_mul_right this (by decide)
  · have : x * 2147483648 < (t * 3329 + 2 * 3329) * 2147483648 := by
      have e : x * 645083 * 3329 + x * 2341 = x * 2147483648 := by
        rw [Nat.mul_assoc, ← Nat.mul_add]
      have h3 : x * 645083 * 3329 < (t * 2147483648 + 2147483648) * 3329 :=
        Nat.mul_lt_mul_of_pos_right h2 (by decide)
      have h4 : x * 2341 < 3329 * 2147483648 :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx (by decide)) (by decide)
      calc x * 2147483648 = x * 645083 * 3329 + x * 2341 := e.symm
        _ < (t * 2147483648 + 2147483648) * 3329 + 3329 * 2147483648 := Nat.add_lt_add h3 h4
        _ = (t * 3329 + 2 * 3329) * 2147483648 := barrett_sum t
    exact Nat.lt_of_mul_lt_mul_right this

/-! ## Lanes as numbers -/

/-- The lanes of `x` are `f 0`, …, `f 3`. -/
def Lanes (x : BitVec 128) (f : Nat → Nat) : Prop := ∀ e < 4, (vword x e).toNat = f e

theorem Lanes.lt {x : BitVec 128} {f : Nat → Nat} (h : Lanes x f) {e : Nat} (he : e < 4) :
    f e < 2 ^ 32 := by rw [← h e he]; exact (vword x e).isLt

theorem Lanes.congr {x : BitVec 128} {f g : Nat → Nat} (h : Lanes x f) (hfg : ∀ e < 4, f e = g e) :
    Lanes x g := fun e he => (h e he).trans (hfg e he)

theorem lanes_add {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a + b) x y) fun e => (f e + g e) % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_add, hx e he, hy e he]

theorem lanes_sub {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a - b) x y) fun e => (2 ^ 32 - g e + f e) % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_sub, hx e he, hy e he]

theorem lanes_mul {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => a * b) x y) fun e => f e * g e % 2 ^ 32 := fun e he => by
  rw [vword_map2 _ _ _ he, BitVec.toNat_mul, hx e he, hy e he]

theorem lanes_umin {x y : BitVec 128} {f g : Nat → Nat} (hx : Lanes x f) (hy : Lanes y g) :
    Lanes (VArr.s4.map2 (fun _ a b => if a.toNat ≤ b.toNat then a else b) x y) fun e => min (f e) (g e) :=
  fun e he => by
    show _ = min (f e) (g e)
    rw [vword_map2 _ _ _ he]
    split <;> rename_i h <;> rw [hx e he, hy e he] at * <;> omega

theorem lanes_mls {a x y : BitVec 128} {h f g : Nat → Nat} (ha : Lanes a h) (hx : Lanes x f)
    (hy : Lanes y g) :
    Lanes (mapWords3 (fun a x y => a - x * y) a x y) fun e => (2 ^ 32 - f e * g e % 2 ^ 32 + h e) % 2 ^ 32 :=
  fun e he => by
    rw [vword_mapWords3 _ _ _ _ he, BitVec.toNat_sub, BitVec.toNat_mul, ha e he, hx e he, hy e he]

theorem lanes_mla {a x y : BitVec 128} {h f g : Nat → Nat} (ha : Lanes a h) (hx : Lanes x f)
    (hy : Lanes y g) :
    Lanes (mapWords3 (fun a x y => a + x * y) a x y) fun e => (h e + f e * g e % 2 ^ 32) % 2 ^ 32 :=
  fun e he => by
    rw [vword_mapWords3 _ _ _ _ he, BitVec.toNat_add, BitVec.toNat_mul, ha e he, hx e he, hy e he]

theorem lanes_dup {w : BitVec 32} : Lanes (ofVWords w w w w) fun _ => w.toNat := fun e he => by
  rw [vword_dup_s4 w he]

theorem eval_sqdmulh {s : State} {d n m : VReg} {f g : Nat → Nat} (hn : Lanes (s.v n) f)
    (hm : Lanes (s.v m) g) (hf : ∀ e < 4, f e < 2 ^ 31) (hg : ∀ e < 4, g e < 2 ^ 31) :
    ∃ x, VOp.eval s (.sqdmulh d n m) = some (d, x) ∧ Lanes x fun e => f e * g e / 2 ^ 31 := by
  have l : ∀ e < 4, sqdmulhLane (vword (s.v n) e) (vword (s.v m) e) =
      some (BitVec.ofNat 32 (f e * g e / 2 ^ 31)) := fun e he => by
    rw [sqdmulhLane_lt (by rw [hn e he]; exact hf e he) (by rw [hm e he]; exact hg e he), hn e he, hm e he]
  refine ⟨ofVWords (BitVec.ofNat 32 (f 0 * g 0 / 2 ^ 31)) (BitVec.ofNat 32 (f 1 * g 1 / 2 ^ 31))
      (BitVec.ofNat 32 (f 2 * g 2 / 2 ^ 31)) (BitVec.ofNat 32 (f 3 * g 3 / 2 ^ 31)),
    by simp only [VOp.eval, l 0 (by decide), l 1 (by decide), l 2 (by decide), l 3 (by decide)],
    fun e he => ?_⟩
  have hl : f e * g e / 2 ^ 31 < 2 ^ 32 := by
    have h1 := hf e he
    have h2 := hg e he
    exact Nat.lt_of_le_of_lt (Nat.div_le_div_right (c := 2 ^ 31)
      (Nat.mul_le_mul (Nat.le_of_lt h1) (Nat.le_of_lt h2))) (by decide)
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]

/-! ## The arithmetic of the vector code -/

/-- `s'` is `s` but for the vector registers `rs`. -/
structure VChg (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace VChg

theorem refl (rs : List VReg) (s : State) : VChg rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List VReg} {s₁ s₂ s₃ : State} (h₁ : VChg rs s₁ s₂) (h₂ : VChg rs' s₂ s₃) :
    VChg (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.v r hr.2, h₁.v r hr.1],
   h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List VReg} {s s' : State} (h : VChg rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VChg rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List VReg} {s s' : State} (h : VChg rs s s') (r : VReg) (hr : r ∉ rs := by decide) :
    s'.v r = s.v r := h.v r hr

end VChg

theorem VChg.keep {rs : List VReg} {s s' : State} (h : VChg rs s s') : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem VMem.keep {s s' : State} {m : Mem} (h : VMem s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem VUpd.chg {s s' : State} {d : VReg} {x : BitVec 128} (h : VUpd s s' d x) : VChg [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

/-- `q` and `M` in the lanes of `v16` and `v17`. -/
structure VConsts (s : State) : Prop where
  q : Lanes (s.v .v16) fun _ => 3329
  m : Lanes (s.v .v17) fun _ => 645083

theorem VConsts.chg {s s' : State} (h : VConsts s) {rs : List VReg} (hc : VChg rs s s')
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide) : VConsts s' :=
  ⟨by rw [hc.get _ h16]; exact h.q, by rw [hc.get _ h17]; exact h.m⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `vcsub d t`: `d mod q`, for lanes less than `2q`. -/
theorem vcsub_ok {d t : VReg} (hdt : d ≠ t := by decide) (hq : Lanes (s.v .v16) fun _ => 3329)
    {f : Nat → Nat}
    (hf : Lanes (s.v d) f) (hlt : ∀ e < 4, f e < 2 * 3329)
    (k : ∀ s', VChg [t, d] s s' → Lanes (s'.v d) (fun e => f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (vcsub d t ++ rest)) s Q := by
  refine wp_vop (d := t) rfl fun s₁ h₁ => wp_vop (d := d) rfl fun s₂ h₂ => k s₂ (h₁.chg.trans h₂.chg) ?_
  have l₁ := lanes_sub hf hq
  rw [← h₁.v] at l₁
  rw [h₂.v]
  refine (lanes_umin (by rw [h₁.get d hdt]; exact hf) l₁).congr fun e he => ?_
  have := hlt e he
  omega

/-- `vmulq d z t`: `d · z mod q`, for lanes less than `q`. -/
theorem vmulq_ok {d z t : VReg} (hdt : d ≠ t := by decide)
    (ht16 : t ≠ .v16 := by decide) (ht17 : t ≠ .v17 := by decide) (hd16 : d ≠ .v16 := by decide)
    (hd17 : d ≠ .v17 := by decide) (hc : VConsts s) {f g : Nat → Nat}
    (hf : Lanes (s.v d) f) (hf' : ∀ e < 4, f e < 3329) (hg : Lanes (s.v z) g) (hg' : ∀ e < 4, g e < 3329)
    (k : ∀ s', VChg [d, t, d, t, d] s s' → Lanes (s'.v d) (fun e => f e * g e % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vmulq d z t ++ rest)) s Q := by
  have hfg : ∀ e < 4, f e * g e < 3329 * 3329 := fun e he =>
    Nat.mul_lt_mul_of_lt_of_lt (hf' e he) (hg' e he)
  refine wp_vop (d := d) rfl fun s₁ h₁ => ?_
  have l₁ : Lanes (s₁.v d) fun e => f e * g e := by
    rw [h₁.v]
    exact (lanes_mul hf hg).congr fun e he => Nat.mod_eq_of_lt (by have := hfg e he; omega)
  have c₁ := hc.chg h₁.chg (by simpa using hd16.symm) (by simpa using hd17.symm)
  obtain ⟨x₂, e₂, l₂⟩ := eval_sqdmulh (d := t) l₁ c₁.m (fun e he => by have := hfg e he; omega)
    (fun _ _ => by decide)
  refine wp_vop e₂ fun s₂ h₂ => ?_
  have c₂ := c₁.chg h₂.chg (by simpa using ht16.symm) (by simpa using ht17.symm)
  refine wp_vop (d := d) rfl fun s₃ h₃ => ?_
  have c₃ := c₂.chg h₃.chg (by simpa using hd16.symm) (by simpa using hd17.symm)
  have a₂ : Lanes (s₂.v d) fun e => f e * g e := by rw [h₂.get d hdt]; exact l₁
  have b₂ : Lanes (s₂.v t) fun e => f e * g e * 645083 / 2 ^ 31 := by rw [h₂.v]; exact l₂
  have l₃ := lanes_mls a₂ b₂ c₂.q
  rw [← h₃.v] at l₃
  have hb : ∀ e < 4, f e * g e * 645083 / 2 ^ 31 * 3329 ≤ f e * g e ∧
      f e * g e < f e * g e * 645083 / 2 ^ 31 * 3329 + 2 * 3329 := fun e he =>
    barrett_nat (by have := hfg e he; omega)
  refine vcsub_ok hdt c₃.q (f := fun e => f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329)
    (l₃.congr fun e he => ?_) (fun e he => ?_) fun s₄ h₄ l₄ =>
    k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄) (l₄.congr fun e he => ?_)
  · show _ = f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329
    have := hb e he
    have : f e * g e * 645083 / 2 ^ 31 * 3329 % 2 ^ 32 = f e * g e * 645083 / 2 ^ 31 * 3329 :=
      Nat.mod_eq_of_lt (by have := hfg e he; omega)
    omega
  · have := hb e he; omega
  · show (f e * g e - f e * g e * 645083 / 2 ^ 31 * 3329) % 3329 = f e * g e % 3329
    have hb' := (hb e he).1
    rw [Nat.mul_comm] at hb'
    rw [Nat.mul_comm _ 3329, Nat.sub_mul_mod hb']

/-- `vbfly z`: the butterflies of Algorithm 9 on the lanes of `v0` and `v1`. -/
theorem vbfly_ok {z : VReg} (hc : VConsts s) {A B Z : Nat → Nat} (hA : Lanes (s.v .v0) A) (hA' : ∀ e < 4, A e < 3329)
    (hB : Lanes (s.v .v1) B) (hB' : ∀ e < 4, B e < 3329) (hZ : Lanes (s.v z) Z)
    (hZ' : ∀ e < 4, Z e < 3329)
    (k : ∀ s', VChg [.v1, .v2, .v3, .v4] s s' →
      Lanes (s'.v .v2) (fun e => (A e + B e * Z e % 3329) % 3329) →
      Lanes (s'.v .v1) (fun e => (A e + (3329 - B e * Z e % 3329)) % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vbfly z ++ rest)) s Q := by
  simp only [vbfly, List.append_assoc, List.cons_append]
  refine vmulq_ok (hc := hc) (hf := hB) (hf' := hB') (hg := hZ) (hg' := hZ')
    (k := fun s₁ h₁ l₁ => ?_)
  have c₁ := hc.chg h₁
  have t₁ : ∀ e < 4, B e * Z e % 3329 < 3329 := fun e _ => Nat.mod_lt _ (by decide)
  refine wp_vop (d := .v2) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v .v0) A := by rw [h₁.get .v0]; exact hA
  have l₂ := lanes_add a₁ l₁
  rw [← h₂.v] at l₂
  refine vcsub_ok (by decide) (c₁.chg h₂.chg).q (f := fun e => (A e + B e * Z e % 3329) % 2 ^ 32) l₂ (fun e he => ?_) fun s₃ h₃ l₃ => ?_
  · have := hA' e he; have := t₁ e he; omega
  refine wp_vop (d := .v3) rfl fun s₄ h₄ => wp_vop (d := .v4) rfl fun s₅ h₅ => wp_vop (d := .v1) rfl
    fun s₆ h₆ => ?_
  have e0 : s₃.v .v0 = s.v .v0 := by rw [h₃.get .v0, h₂.get .v0, h₁.get .v0]
  have e1 : s₃.v .v1 = s₁.v .v1 := by rw [h₃.get .v1, h₂.get .v1]
  have a₃ : Lanes (s₃.v .v0) A := by rw [e0]; exact hA
  have b₃ : Lanes (s₃.v .v1) fun e => B e * Z e % 3329 := by rw [e1]; exact l₁
  have l₄ := lanes_sub a₃ b₃
  rw [← h₄.v] at l₄
  have l₅ := lanes_add l₄ (c₁.chg ((h₂.chg.trans h₃).trans h₄.chg)).q
  rw [← h₅.v] at l₅
  have a₅ : Lanes (s₅.v .v3) fun e => (2 ^ 32 - B e * Z e % 3329 + A e) % 2 ^ 32 := by
    rw [h₅.get .v3]; exact l₄
  have l₆ := lanes_umin a₅ l₅
  rw [← h₆.v] at l₆
  refine k s₆ (((((h₁.trans h₂.chg).trans h₃).trans h₄.chg).trans h₅.chg).trans h₆.chg |>.mono)
    (by rw [h₆.get .v2, h₅.get .v2, h₄.get .v2]
        exact l₃.congr fun e he => by
          show (A e + B e * Z e % 3329) % 2 ^ 32 % 3329 = _
          have := hA' e he; have := t₁ e he
          rw [Nat.mod_eq_of_lt (show A e + B e * Z e % 3329 < 2 ^ 32 by omega)])
    (l₆.congr fun e he => ?_)
  have := hA' e he; have := t₁ e he
  show min _ _ = _
  omega

/-- `vibfly z`: the butterflies of Algorithm 10 on the lanes of `v0` and `v1`. -/
theorem vibfly_ok {z : VReg} (hz : z ∉ [VReg.v0, .v1, .v2, .v3, .v4, .v16, .v17] := by decide)
    (hc : VConsts s) {A B Z : Nat → Nat} (hA : Lanes (s.v .v0) A) (hA' : ∀ e < 4, A e < 3329)
    (hB : Lanes (s.v .v1) B) (hB' : ∀ e < 4, B e < 3329) (hZ : Lanes (s.v z) Z)
    (hZ' : ∀ e < 4, Z e < 3329)
    (k : ∀ s', VChg [.v1, .v2, .v3] s s' →
      Lanes (s'.v .v2) (fun e => (A e + B e) % 3329) →
      Lanes (s'.v .v1) (fun e => (B e + (3329 - A e)) % 3329 * Z e % 3329) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (vibfly z ++ rest)) s Q := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  simp only [vibfly, List.append_assoc, List.cons_append]
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ := lanes_add hA hB
  rw [← h₁.v] at l₁
  refine vcsub_ok (by decide) (hc.chg h₁.chg).q (f := fun e => (A e + B e) % 2 ^ 32) l₁ (fun e he => ?_) fun s₂ h₂ l₂ => ?_
  · have := hA' e he; have := hB' e he; omega
  have c₂ := hc.chg (h₁.chg.trans h₂)
  refine wp_vop (d := .v1) rfl fun s₃ h₃ => wp_vop (d := .v3) rfl fun s₄ h₄ => wp_vop (d := .v1) rfl
    fun s₅ h₅ => ?_
  have e0 : s₂.v .v0 = s.v .v0 := by rw [h₂.get .v0, h₁.get .v0]
  have e1 : s₂.v .v1 = s.v .v1 := by rw [h₂.get .v1, h₁.get .v1]
  have a₂ : Lanes (s₂.v .v1) B := by rw [e1]; exact hB
  have b₂ : Lanes (s₂.v .v0) A := by rw [e0]; exact hA
  have l₃ := lanes_sub a₂ b₂
  rw [← h₃.v] at l₃
  have l₄ := lanes_add l₃ (c₂.chg h₃.chg).q
  rw [← h₄.v] at l₄
  have a₄ : Lanes (s₄.v .v1) fun e => (2 ^ 32 - A e + B e) % 2 ^ 32 := by
    rw [h₄.get .v1]; exact l₃
  have l₅ := lanes_umin a₄ l₄
  rw [← h₅.v] at l₅
  have c₅ := c₂.chg ((h₃.chg.trans h₄.chg).trans h₅.chg)
  have d₅ : ∀ e < 4, min ((2 ^ 32 - A e + B e) % 2 ^ 32) (((2 ^ 32 - A e + B e) % 2 ^ 32 + 3329) % 2 ^ 32) =
      (B e + (3329 - A e)) % 3329 := fun e he => by
    have := hA' e he; have := hB' e he; omega
  have z₅ : Lanes (s₅.v z) Z := by
    rw [h₅.get z hz.2.1, h₄.get z hz.2.2.2.1, h₃.get z hz.2.1, h₂.v z (by simp [hz.2.2.1, hz.2.2.2.1]),
      h₁.get z hz.2.2.1]
    exact hZ
  refine vmulq_ok (d := .v1) (z := z) (t := .v3) (hc := c₅) (hf := l₅.congr d₅)
    (hf' := fun e _ => Nat.mod_lt _ (by decide)) (hg := z₅) (hg' := hZ') (k := fun s₆ h₆ l₆ => ?_)
  refine k s₆ ((((h₁.chg.trans h₂).trans h₃.chg).trans h₄.chg).trans h₅.chg |>.trans h₆ |>.mono)
    (by rw [h₆.get .v2, h₅.get .v2, h₄.get .v2, h₃.get .v2]
        exact l₂.congr fun e he => by
          show (A e + B e) % 2 ^ 32 % 3329 = _
          have := hA' e he; have := hB' e he
          rw [Nat.mod_eq_of_lt (show A e + B e < 2 ^ 32 by omega)]) l₆

/-- `sqdmulh t, d, M; mls d, t, q`: Barrett reduction of lanes `x < 2³¹`, to
`x - ⌊x · M / 2³¹⌋ · q`, which is less than `2q` and congruent to `x`. -/
theorem vbar_ok {d t : VReg} (hdt : d ≠ t := by decide) (ht16 : t ≠ .v16 := by decide)
    (ht17 : t ≠ .v17 := by decide) (hc : VConsts s) {f : Nat → Nat} (hf : Lanes (s.v d) f)
    (hlt : ∀ e < 4, f e < 2 ^ 31)
    (k : ∀ s', VChg [t, d] s s' →
      Lanes (s'.v d) (fun e => f e - f e * 645083 / 2 ^ 31 * 3329) →
      (∀ e < 4, f e - f e * 645083 / 2 ^ 31 * 3329 < 2 * 3329 ∧
        (f e - f e * 645083 / 2 ^ 31 * 3329) % 3329 = f e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (.vop (.sqdmulh t d .v17) :: .vop (.mls d t .v16) :: rest)) s Q := by
  obtain ⟨x₁, e₁, l₁⟩ := eval_sqdmulh (d := t) hf hc.m hlt (fun _ _ => by decide)
  refine wp_vop e₁ fun s₁ h₁ => ?_
  have c₁ := hc.chg h₁.chg (by simpa using ht16.symm) (by simpa using ht17.symm)
  refine wp_vop (d := d) rfl fun s₂ h₂ => ?_
  have a₁ : Lanes (s₁.v d) f := by rw [h₁.get d hdt]; exact hf
  have b₁ : Lanes (s₁.v t) fun e => f e * 645083 / 2 ^ 31 := by rw [h₁.v]; exact l₁
  have l₂ := lanes_mls a₁ b₁ c₁.q
  rw [← h₂.v] at l₂
  have hb : ∀ e < 4, f e * 645083 / 2 ^ 31 * 3329 ≤ f e ∧
      f e < f e * 645083 / 2 ^ 31 * 3329 + 2 * 3329 := fun e he => barrett_nat (hlt e he)
  refine k s₂ (h₁.chg.trans h₂.chg) (l₂.congr fun e he => ?_) fun e he => ⟨?_, ?_⟩
  · show _ = f e - f e * 645083 / 2 ^ 31 * 3329
    have := hb e he
    have : f e * 645083 / 2 ^ 31 * 3329 % 2 ^ 32 = f e * 645083 / 2 ^ 31 * 3329 :=
      Nat.mod_eq_of_lt (by have := hlt e he; omega)
    have := hlt e he
    omega
  · have := hb e he; omega
  · have hb' := (hb e he).1
    rw [Nat.mul_comm] at hb'
    rw [Nat.mul_comm _ 3329, Nat.sub_mul_mod hb']

end

end VG.Proof.MlKem.AArch64
