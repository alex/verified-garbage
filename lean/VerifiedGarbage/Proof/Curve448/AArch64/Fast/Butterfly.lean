import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sub
import VerifiedGarbage.Proof.X448.AArch64.Swap

/-!
# The ladder's sums and differences, of conditionally swapped coordinates

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq mask xor_sel)
open VG.Proof.Ed25519.AArch64 (read_x)

def bflyBody (x2 z2 x3 z3 a b c d i : Nat) : List Instr :=
  [ld .x4 (x2 + 8 * i), ld .x7 (x3 + 8 * i), ld .x5 (z2 + 8 * i), ld .x8 (z3 + 8 * i),
    .logic .eor .x .x9 .x4 .x7, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x4 .x4 .x9, .logic .eor .x .x7 .x7 .x9,
    .logic .eor .x .x9 .x5 .x8, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x5 .x5 .x9, .logic .eor .x .x8 .x8 .x9,
    .add .x .x9 .x4 .x5, st .x9 (a + 8 * i),
    .add .x .x10 .x4 (twoPReg i), .sub .x .x10 .x10 .x5, st .x10 (b + 8 * i),
    .add .x .x11 .x7 .x8, st .x11 (c + 8 * i),
    .add .x .x13 .x7 (twoPReg i), .sub .x .x13 .x13 .x8, st .x13 (d + 8 * i)]

theorem butterfly_split (x2 z2 x3 z3 a b c d : Nat) :
    butterfly x2 z2 x3 z3 a b c d = twoPRegs ++ (List.range 8).flatMap (bflyBody x2 z2 x3 z3 a b c d) :=
  rfl

/-- The swapped words. -/
def sel (sw : Bool) (p q : BitVec 64) : BitVec 64 := if sw then q else p

theorem bflyStep_ok {t : State} {base : Addr} (ht : Scr t base) {x2 z2 x3 z3 a b c d i : Nat}
    (hi : i < 8) (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) {sw : Bool} (hm : t.gpr .x6 = mask sw) :
    WP isa (.block (bflyBody x2 z2 x3 z3 a b c d i)) t fun u =>
      let X2 := sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
      let X3 := sel sw (word t.mem base (x3 + 8 * i)) (word t.mem base (x2 + 8 * i))
      let Z2 := sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
      let Z3 := sel sw (word t.mem base (z3 + 8 * i)) (word t.mem base (z2 + 8 * i))
      u.mem = (((t.mem.writeW (off base (a + 8 * i)) (X2 + Z2)).writeW (off base (b + 8 * i))
        (X2 + twoPW i - Z2)).writeW (off base (c + 8 * i)) (X3 + Z3)).writeW (off base (d + 8 * i))
        (X3 + twoPW i - Z3) ∧
      Keeps [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] t u := by
  have g : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], (e + 8 * i) % 8 = 0 ∧ e + 8 * i < 4096 * 8 ∧
      InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 (e + 8 * i)) 8 ∧
      InRegions t.wr (base + BitVec.ofNat 64 (e + 8 * i)) 8 := fun e he => by
    have := h e he
    exact ⟨by omega, by omega, ht.read (by omega), ht.write (by omega)⟩
  obtain ⟨ax2, bx2, rx2, -⟩ := g x2 (by simp)
  obtain ⟨az2, bz2, rz2, -⟩ := g z2 (by simp)
  obtain ⟨ax3, bx3, rx3, -⟩ := g x3 (by simp)
  obtain ⟨az3, bz3, rz3, -⟩ := g z3 (by simp)
  obtain ⟨aa, ba, -, wa⟩ := g a (by simp)
  obtain ⟨ab, bb, -, wb⟩ := g b (by simp)
  obtain ⟨ac, bc, -, wc⟩ := g c (by simp)
  obtain ⟨ad, bd, -, wd⟩ := g d (by simp)
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x7 ∧ twoPReg i ≠ .x8 ∧
      twoPReg i ≠ .x9 ∧ twoPReg i ≠ .x10 ∧ twoPReg i ≠ .x11 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [bflyBody, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, ax2, bx2, ax3, bx3, az2, bz2, az3, bz3,
      aa, ba, ab, bb, ac, bc, ad, bd, rx2, rx3, rz2, rz3, wa, wb, wc, wd, and_self, Option.map_some,
      Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · have sx := xor_sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
    have sz := xor_sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
    simp only [word, off] at sx sz
    simp only [tw.1, tw.2.1, tw.2.2.1, tw.2.2.2.1, tw.2.2.2.2.1,
      tw.2.2.2.2.2.1, tw.2.2.2.2.2.2, ite_false, BitVec.setWidth_eq, write8_eq,
      read8_eq, word, off, hm, sx.1, sx.2, sz.1, sz.2, twoPReg_val h0 h2, sel]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    simp only [RegUpd.gpr_write, q1, q2, q3, q4, q5, q6, q7, q8, ite_false]

/-- Slots `x` and `y` (64 bytes each) are disjoint. -/
abbrev Dj (x y : Nat) : Prop := x + 64 ≤ y ∨ y + 64 ≤ x

theorem word_w4 (m : Mem) (base : Addr) {p q r t d : Nat} (v₁ v₂ v₃ v₄ : BitVec 64)
    (hp : p + 8 ≤ 8192) (hq : q + 8 ≤ 8192) (hr : r + 8 ≤ 8192) (ht : t + 8 ≤ 8192) (hd : d + 8 ≤ 8192)
    (sp : d = p ∨ d + 8 ≤ p ∨ p + 8 ≤ d) (sq : d = q ∨ d + 8 ≤ q ∨ q + 8 ≤ d)
    (sr : d = r ∨ d + 8 ≤ r ∨ r + 8 ≤ d) (st' : d = t ∨ d + 8 ≤ t ∨ t + 8 ≤ d) :
    word ((((m.writeW (off base p) v₁).writeW (off base q) v₂).writeW (off base r) v₃).writeW
      (off base t) v₄) base d =
      if d = t then v₄ else if d = r then v₃ else if d = q then v₂ else if d = p then v₁ else
        word m base d := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ ht hd st',
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hr hd sr,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hq hd sq,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hp hd sp]

def bflyV (m : Mem) (base : Addr) (sw : Bool) (x2 z2 x3 z3 a b c : Nat) (o i : Nat) : BitVec 64 :=
  let X2 := sel sw (word m base (x2 + 8 * i)) (word m base (x3 + 8 * i))
  let X3 := sel sw (word m base (x3 + 8 * i)) (word m base (x2 + 8 * i))
  let Z2 := sel sw (word m base (z2 + 8 * i)) (word m base (z3 + 8 * i))
  let Z3 := sel sw (word m base (z3 + 8 * i)) (word m base (z2 + 8 * i))
  if o = a then X2 + Z2 else if o = b then X2 + twoPW i - Z2 else if o = c then X3 + Z3
  else X3 + twoPW i - Z3

theorem butterfly_ok {s : State} {base : Addr} (hs : Scr s base) {x2 z2 x3 z3 a b c d : Nat}
    (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (hout : ∀ o ∈ [a, b, c, d], ∀ o' ∈ [a, b, c, d], o ≠ o' → Dj o o')
    (hin : ∀ o ∈ [a, b, c, d], ∀ e ∈ [x2, z2, x3, z3], Dj o e)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (butterfly x2 z2 x3 z3 a b c d)) s fun t =>
      (∀ o ∈ [a, b, c, d], ∀ i < 8, word t.mem base (o + 8 * i) = bflyV s.mem base sw x2 z2 x3 z3 a b c o i) ∧
      (∀ x, Away base [a, b, c, d] 64 x → t.mem x = s.mem x) ∧
      Keeps [.x0, .x2, .x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] s t := by
  rw [butterfly_split, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have h6 : t.gpr .x6 = mask sw := by rw [tk.1 _ (by decide), hm]
  have hb := fun e (he : e ∈ [x2, z2, x3, z3, a, b, c, d]) => h e he
  have ha' := hb a (by simp); have hb' := hb b (by simp); have hc' := hb c (by simp)
  have hd' := hb d (by simp)
  have dab := hout a (by simp) b (by simp) hab; have dac := hout a (by simp) c (by simp) hac
  have dad := hout a (by simp) d (by simp) had; have dbc := hout b (by simp) c (by simp) hbc
  have dbd := hout b (by simp) d (by simp) hbd; have dcd := hout c (by simp) d (by simp) hcd
  have := limbs_loop (base := base) (outs := [a, b, c, d]) (rs := [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13])
    (body := bflyBody x2 z2 x3 z3 a b c d)
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4 ∧ u.gpr .x6 = mask sw)
    (fun u v ⟨h0, h2, h6⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2,
      (k.1 _ (by decide)).trans h6⟩) (by decide)
    (bflyV t.mem base sw x2 z2 x3 z3 a b c) t
    (fun i hi u us ⟨h0, h2, h6⟩ hm' => WP.mono (bflyStep_ok us hi h h0 h2 h6)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => ?_, fun x hx => ?_, wk⟩)
    (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> omega) hout ts ⟨t0, t2, h6⟩
  · refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun o ho i hi => ?_, fun x hx => by rw [um x hx, tm],
      (tk.mono (by decide)).trans (uk.mono (by decide))⟩
    rw [uv o ho i hi]; simp only [bflyV, tm]
  · have e : ∀ q ∈ [x2, z2, x3, z3], word u.mem base (q + 8 * i) = word t.mem base (q + 8 * i) := by
      intro q hq
      have := (h q (List.mem_append_left [a, b, c, d] (by exact hq))).1
      exact away_word hm' (by omega) (fun o ho => by have := hin o ho q hq; simp only [Dj] at this; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
    rw [wm]
    rcases ho' with rfl | rfl | rfl | rfl
    all_goals
      rw [word_w4 _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simp only [bflyV, e x2 (by simp), e z2 (by simp), e x3 (by simp), e z3 (by simp)]
    all_goals split_ifs <;> first | (exfalso; omega) | rfl
  · rw [wm]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [writeW_frame _ (by omega) _ x hx.2.2.2, writeW_frame _ (by omega) _ x hx.2.2.1,
      writeW_frame _ (by omega) _ x hx.2.1, writeW_frame _ (by omega) _ x hx.1]

end VG.Proof.Curve448.AArch64.Fast
