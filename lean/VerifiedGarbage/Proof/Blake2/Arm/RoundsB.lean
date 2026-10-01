import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.Arm.CompressB

/-!
# BLAKE2b on ARMv7: the rounds

Untrusted: everything here is checked by Lean. Weakest-precondition rules for
the 64-bit operations `G` uses on pairs of 32-bit registers (exclusive or and
rotations; loads, stores and additions are SHA-512's,
`Proof/Sha512/Arm/Rounds.lean`), in continuation-passing style; `G`, executed
once for any offsets of its words and message words (`wp_g`); and the rounds
on the work vector in `scratch[0, 128)`.
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr' g gAt round rounds)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A Reg64 Wrote wp_st wp_add64 wp_eor mem_rd lo_xor hi_xor
  lo_rotr hi_rotr lo_rotr' hi_rotr' lo_rd64 hi_rd64 eq_of_lo_hi rd64_write64_self rd64_write64_ne
  frame_write64 rd64_frame)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_ldr op2_reg op2_lsr op2_lsl)
open VG.Spec.Blake2 (Work Block)

/-! ## Rotations by 32 -/

theorem lo_rotr32 (x : BitVec 64) : lo (x.rotateRight 32) = hi x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lo, Impl.Sha512.Arm.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight,
    Nat.zero_add, show 32 % 64 = 32 from rfl, show 64 - 32 = 32 from rfl, hi, decide_true,
    Bool.true_and, ite_true]

theorem hi_rotr32 (x : BitVec 64) : hi (x.rotateRight 32) = lo x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lo, Impl.Sha512.Arm.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight,
    Nat.zero_add, show 32 % 64 = 32 from rfl, show 64 - 32 = 32 from rfl, hi, decide_true,
    Bool.true_and, show ¬ 32 + i < 32 by omega, show 32 + i < 64 by omega, ite_false,
    Nat.add_sub_cancel_left]

/-- A word rotated by 32 is its halves swapped. -/
theorem pair_swap {s : State} {l h : Reg} {x : BitVec 64} (p : Pair s l h x) :
    Pair s h l (x.rotateRight 32) :=
  ⟨by rw [lo_rotr32]; exact p.2, by rw [hi_rotr32]; exact p.1⟩

/-! ## The 64-bit operations -/

/-- The registers a region of 64-bit words can be read through. -/
def Rd64 (rs : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 8 ≤ N → InRegions rs (A B o) 4 ∧ InRegions rs (A B (o + 4)) 4

theorem Reg64.rd {wr : List Region} {B : BitVec 32} {N : Nat} (rd : List Region) (h : Reg64 wr B N) :
    Rd64 (rd ++ wr) B N :=
  fun o ho => ⟨mem_rd' (h o ho).1, mem_rd' (h o ho).2⟩
where
  mem_rd' {a : Addr} {n : Nat} : InRegions wr a n → InRegions (rd ++ wr) a n :=
    fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- A load of a 64-bit word from readable memory, whose contents are `m`. -/
theorem wp_ld64 {l h b : Reg} {B : BitVec 32} {off : Nat} {m : Mem} (hlb : l ≠ b) (hlh : l ≠ h)
    (ho : off + 4 < 4096) (hb : s.gpr b = B) (hm : s.mem = m)
    (hi : InRegions (s.rd ++ s.wr) (A B off) 4) (hi' : InRegions (s.rd ++ s.wr) (A B (off + 4)) 4)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h (rd64 m B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h b off ++ rest)) s Q := by
  subst hm
  simp only [ld, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) hi fun s₁ u₁ => ?_
  refine wp_ldr ho (by rw [u₁.other b (Ne.symm hlb), hb]) (by rw [u₁.rd, u₁.wr]; exact hi')
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, lo_rd64]
  · rw [u₂.gpr, u₁.mem, hi_rd64]

theorem wp_xor64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x ^^^ y) → WP isa (.block rest) s' Q) :
    WP isa (.block (xor64 dl dh l h ++ rest)) s Q := by
  simp only [xor64, List.cons_append, List.nil_append]
  refine wp_eor (op2_reg _ _) fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_xor]
  · rw [u₂.gpr, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.2, py.2, hi_xor]

theorem wp_rotr {n : Nat} {t l h : Reg} {x : BitVec 64} (h0 : 0 < n) (hn : n < 32)
    (htl : t ≠ l) (hth : t ≠ h) (hlh : l ≠ h) (px : Pair s l h x)
    (k : ∀ s', Only [t, h] s s' → Pair s' t h (x.rotateRight n) → WP isa (.block rest) s' Q) :
    WP isa (.block (rotr n t l h ++ rest)) s Q := by
  simp only [rotr, List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr ⟨h0, by omega⟩) fun s₁ u₁ => ?_
  refine wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsr ⟨h0, by omega⟩) fun s₃ u₃ => ?_
  refine wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₄ u₄ =>
    k s₄ (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other t hth, u₃.other t hth, u₂.gpr, u₁.gpr, u₁.other h (Ne.symm hth), px.1, px.2,
      lo_rotr x h0 hn]
  · rw [u₄.gpr, u₃.gpr, u₃.other l hlh, u₂.other h (Ne.symm hth), u₂.other l (Ne.symm htl),
      u₁.other h (Ne.symm hth), u₁.other l (Ne.symm htl), px.1, px.2, hi_rotr x h0 hn]

theorem wp_rotr' {n : Nat} {t l h : Reg} {x : BitVec 64} (h0 : 32 < n) (hn : n < 64)
    (htl : t ≠ l) (hth : t ≠ h) (hlh : l ≠ h) (px : Pair s l h x)
    (k : ∀ s', Only [t, h] s s' → Pair s' t h (x.rotateRight n) → WP isa (.block rest) s' Q) :
    WP isa (.block (rotr' n t l h ++ rest)) s Q := by
  simp only [rotr', List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr ⟨by omega, by omega⟩) fun s₁ u₁ => ?_
  refine wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsl ⟨by omega, by omega⟩) fun s₃ u₃ => ?_
  refine wp_eor (op2_lsr ⟨by omega, by omega⟩) fun s₄ u₄ =>
    k s₄ (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other t hth, u₃.other t hth, u₂.gpr, u₁.gpr, u₁.other l (Ne.symm htl), px.1, px.2,
      lo_rotr' x h0 hn]
  · rw [u₄.gpr, u₃.gpr, u₃.other l hlh, u₂.other h (Ne.symm hth), u₂.other l (Ne.symm htl),
      u₁.other h (Ne.symm hth), u₁.other l (Ne.symm htl), px.1, px.2, hi_rotr' x h0 hn,
      BitVec.xor_comm]

end

/-! ## One `G` -/

/-- The registers `G` writes. -/
def gRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The memory after `G` on the words at `V + a`, …, `V + d`, with the message
words at `Bk + x` and `Bk + y`. -/
def gMem (m : Mem) (V Bk : BitVec 32) (a b c d x y : Nat) : Mem :=
  let r := mix Spec.Blake2.b (rd64 m V a) (rd64 m V b) (rd64 m V c) (rd64 m V d) (rd64 m Bk x)
    (rd64 m Bk y)
  write64 (write64 (write64 (write64 m V a r.1) V b r.2.1) V c r.2.2.1) V d r.2.2.2

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_g {a b c d x y : Nat} {V Bk : BitVec 32}
    (ha : a + 8 ≤ 128) (hb : b + 8 ≤ 128) (hc : c + 8 ≤ 128) (hd : d + 8 ≤ 128)
    (hx : x + 8 ≤ 128) (hy : y + 8 ≤ 128)
    (hRV : Reg64 s.wr V 128) (hRB : Rd64 (s.rd ++ s.wr) Bk 128) (h3 : s.gpr .r3 = V)
    (h1 : s.gpr .r1 = Bk)
    (K : ∀ s', Wrote gRegs s s' (gMem s.mem V Bk a b c d x y) → WP isa (.block rest) s' Q) :
    WP isa (.block (g a b c d x y ++ rest)) s Q := by
  unfold g
  simp only [List.append_assoc]
  have iV : ∀ o, o + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (A V o) 4 ∧
      InRegions (s.rd ++ s.wr) (A V (o + 4)) 4 := Reg64.rd s.rd hRV
  -- Load the four words.
  refine wp_ld64 (by decide) (by decide) (by omega) h3 rfl (iV a ha).1 (iV a ha).2
    fun s₁ o₁ pa => ?_
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3]) o₁.mem
    (by rw [o₁.rd, o₁.wr]; exact (iV b hb).1) (by rw [o₁.rd, o₁.wr]; exact (iV b hb).2)
    fun s₂ o₂ pb => ?_
  have O₂ := o₁.trans o₂
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), h3]) O₂.mem
    (by rw [O₂.rd, O₂.wr]; exact (iV c hc).1) (by rw [O₂.rd, O₂.wr]; exact (iV c hc).2)
    fun s₃ o₃ pc => ?_
  have O₃ := O₂.trans o₃
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), h3]) O₃.mem
    (by rw [O₃.rd, O₃.wr]; exact (iV d hd).1) (by rw [O₃.rd, O₃.wr]; exact (iV d hd).2)
    fun s₄ o₄ pd => ?_
  have O₄ := O₃.trans o₄
  -- a := a + b + m[x]
  refine wp_add64 (by decide) (by decide)
    (pa.of_only ((o₂.trans o₃).trans o₄) (by decide) (by decide))
    (pb.of_only (o₃.trans o₄) (by decide) (by decide)) fun s₅ o₅ p₅ => ?_
  have O₅ := O₄.trans o₅
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₅.gpr _ (by decide), h1]) O₅.mem
    (by rw [O₅.rd, O₅.wr]; exact (hRB x hx).1) (by rw [O₅.rd, O₅.wr]; exact (hRB x hx).2)
    fun s₆ o₆ pX => ?_
  refine wp_add64 (by decide) (by decide) (p₅.of_only o₆ (by decide) (by decide)) pX
    fun s₇ o₇ p₇ => ?_
  -- d := (d ⊕ a) >>> 32
  refine wp_xor64 (by decide) (by decide)
    (pd.of_only (((o₅.trans o₆).trans o₇)) (by decide) (by decide)) p₇ fun s₈ o₈ p₈ => ?_
  have pd₁ := pair_swap p₈
  -- c := c + d
  refine wp_add64 (by decide) (by decide)
    (pc.of_only ((((o₄.trans o₅).trans o₆).trans o₇).trans o₈) (by decide) (by decide)) pd₁
    fun s₉ o₉ pc₁ => ?_
  -- b := (b ⊕ c) >>> 24
  refine wp_xor64 (by decide) (by decide)
    (pb.of_only ((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉) (by decide)
      (by decide)) pc₁ fun s₁₀ o₁₀ p₁₀ => ?_
  refine wp_rotr (n := 24) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₀
    fun s₁₁ o₁₁ pb₁ => ?_
  have O₁₁ := (((((((O₅.trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀).trans o₁₁))
  -- a := a + b + m[y]
  refine wp_ld64 (by decide) (by decide) (by omega) (by rw [O₁₁.gpr _ (by decide), h1]) O₁₁.mem
    (by rw [O₁₁.rd, O₁₁.wr]; exact (hRB y hy).1) (by rw [O₁₁.rd, O₁₁.wr]; exact (hRB y hy).2)
    fun s₁₂ o₁₂ pY => ?_
  refine wp_add64 (by decide) (by decide)
    (p₇.of_only ((((o₈.trans o₉).trans o₁₀).trans o₁₁).trans o₁₂) (by decide) (by decide))
    (pb₁.of_only o₁₂ (by decide) (by decide)) fun s₁₃ o₁₃ p₁₃ => ?_
  refine wp_add64 (by decide) (by decide) p₁₃ (pY.of_only o₁₃ (by decide) (by decide))
    fun s₁₄ o₁₄ pa₂ => ?_
  -- d := (d ⊕ a) >>> 16
  refine wp_xor64 (by decide) (by decide)
    (pd₁.of_only (((((o₉.trans o₁₀).trans o₁₁).trans o₁₂).trans o₁₃).trans o₁₄) (by decide)
      (by decide)) pa₂ fun s₁₅ o₁₅ p₁₅ => ?_
  refine wp_rotr (n := 16) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₅
    fun s₁₆ o₁₆ pd₂ => ?_
  -- c := c + d
  refine wp_add64 (by decide) (by decide)
    (pc₁.of_only ((((((o₁₀.trans o₁₁).trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆)
      (by decide) (by decide)) pd₂ fun s₁₇ o₁₇ pc₂ => ?_
  -- b := (b ⊕ c) >>> 63
  refine wp_xor64 (by decide) (by decide)
    (pb₁.of_only ((((((o₁₂.trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).trans o₁₇)) (by decide)
      (by decide)) pc₂ fun s₁₈ o₁₈ p₁₈ => ?_
  refine wp_rotr' (n := 63) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₈
    fun s₁₉ o₁₉ pb₂ => ?_
  have O₁₉ := (((((((((O₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).trans o₁₇).trans
    o₁₈).trans o₁₉))
  have pa₂' := pa₂.of_only ((((o₁₅.trans o₁₆).trans o₁₇).trans o₁₈).trans o₁₉) (by decide) (by decide)
  have pc₂' := pc₂.of_only (o₁₈.trans o₁₉) (by decide) (by decide)
  have pd₂' := pd₂.of_only ((o₁₇.trans o₁₈).trans o₁₉) (by decide) (by decide)
  -- Store them.
  have w : Reg64 s₁₉.wr V 128 := by rw [O₁₉.wr]; exact hRV
  have r3 : s₁₉.gpr .r3 = V := by rw [O₁₉.gpr _ (by decide), h3]
  refine wp_st (by omega) r3 pa₂' (w a ha).1 (w a ha).2 fun s₂₀ u₂₀ => ?_
  refine wp_st (by omega) (by rw [u₂₀.gpr, r3]) (by rw [Pair, u₂₀.gpr]; exact pb₂)
    (by rw [u₂₀.wr]; exact (w b hb).1) (by rw [u₂₀.wr]; exact (w b hb).2) fun s₂₁ u₂₁ => ?_
  refine wp_st (by omega) (by rw [u₂₁.gpr, u₂₀.gpr, r3]) (by rw [Pair, u₂₁.gpr, u₂₀.gpr]; exact pc₂')
    (by rw [u₂₁.wr, u₂₀.wr]; exact (w c hc).1) (by rw [u₂₁.wr, u₂₀.wr]; exact (w c hc).2)
    fun s₂₂ u₂₂ => ?_
  refine wp_st (by omega) (by rw [u₂₂.gpr, u₂₁.gpr, u₂₀.gpr, r3])
    (by rw [Pair, u₂₂.gpr, u₂₁.gpr, u₂₀.gpr]; exact pd₂')
    (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr]; exact (w d hd).1)
    (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr]; exact (w d hd).2) fun s₂₃ u₂₃ => K s₂₃ ⟨fun r hr => ?_, ?_,
      by rw [u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, O₁₉.rd], by rw [u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, O₁₉.wr],
      by rw [u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, O₁₉.sp]⟩
  · rw [u₂₃.gpr, u₂₂.gpr, u₂₁.gpr, u₂₀.gpr]
    exact (O₁₉.mono (by decide)).gpr r hr
  · rw [u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, O₁₉.mem]
    rfl

end

/-! ## The work vector in `scratch` -/

theorem rd64_write64 (m : Mem) {V : BitVec 32} (fit : V.toNat + 128 ≤ 2 ^ 32) {o o' : Nat}
    (x : BitVec 64) (ho : o + 8 ≤ 128) (ho' : o' + 8 ≤ 128) (h8 : o % 8 = 0) (h8' : o' % 8 = 0) :
    rd64 (write64 m V o x) V o' = if o = o' then x else rd64 m V o' := by
  by_cases e : o = o'
  · subst e; simp only [ite_true]; exact rd64_write64_self _ _ (by omega)
  · simp only [e, ite_false]; exact rd64_write64_ne _ _ (by omega) (by omega) (by omega)

/-- What the rounds need of the state `s₀` at their start: the scratch space
at `V` (in `r3`), and the message block `M` at `Bk` (in `r1`). -/
structure RCtx (V Bk : BitVec 32) (M : Block 64) (s₀ : State) : Prop where
  r3 : s₀.gpr .r3 = V
  r1 : s₀.gpr .r1 = Bk
  fitV : V.toNat + 128 ≤ 2 ^ 32
  fitB : Bk.toNat + 128 ≤ 2 ^ 32
  wV : Reg64 s₀.wr V 128
  rB : Rd64 (s₀.rd ++ s₀.wr) Bk 128
  disj : Region.Disjoint ⟨State.addr Bk, 128⟩ ⟨State.addr V, 128⟩
  msg : ∀ j (hj : j < 16), rd64 s₀.mem Bk (8 * j) = M ⟨j, hj⟩

/-- The rounds invariant, relative to the state `s₀` at their start: the work
vector `v` is in `scratch[0, 128)`, and nothing else has changed but the
registers of `G`. -/
structure RI (V : BitVec 32) (s₀ : State) (v : Work 64) (s : State) : Prop where
  vars : ∀ k (hk : k < 16), rd64 s.mem V (8 * k) = v[k]
  gpr : ∀ r, r ∉ gRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr V, 128⟩] s₀.mem s.mem

theorem eq_mul8 (p q : Nat) : (8 * p = 8 * q) = (p = q) := propext ⟨fun h => by omega, fun h => by rw [h]⟩

theorem gAt_ok {x y z u : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hu : u < 16)
    (hq : [x, y, z, u].Nodup) (r i : Nat) {V Bk : BitVec 32} {M : Block 64} {s₀ s : State}
    {v : Work 64} (c : RCtx V Bk M s₀) (h : RI V s₀ v s) :
    WP isa (gAt r i x y z u) s (RI V s₀ (Spec.Blake2.G Spec.Blake2.b v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
      ⟨u, hu⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hq
  obtain ⟨⟨nxy, nxz, nxu⟩, ⟨nyz, nyu⟩, nzu, -⟩ := hq
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have fitV := c.fitV
  unfold gAt
  rw [← List.append_nil (g _ _ _ _ _ _)]
  refine wp_g (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [h.wr]; exact c.wV) (by rw [h.rd, h.wr]; exact c.rB) (by rw [h.gpr _ (by decide), c.r3])
    (by rw [h.gpr _ (by decide), c.r1]) fun s' w => WP.block_nil ?_
  have hm : ∀ j (hj : j < 16), rd64 s.mem Bk (8 * j) = M ⟨j, hj⟩ := fun j hj => by
    rw [rd64_frame h.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c.disj)
      c.fitB (by omega)]
    exact c.msg j hj
  refine ⟨fun k hk => ?_, fun q hq => by rw [w.gpr q hq, h.gpr q hq], by rw [w.rd, h.rd],
    by rw [w.wr, h.wr], by rw [w.sp, h.sp], ?_⟩
  · have m8 : ∀ p, (8 * p) % 8 = 0 := fun p => Nat.mul_mod_right 8 p
    rw [w.mem, gMem]
    rw [rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      h.vars x hx, h.vars y hy, h.vars z hz, h.vars u hu, h.vars k hk, hm _ sj, hm _ sk,
      Proof.Blake2.G_get _ v (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (c := ⟨z, hz⟩) (d := ⟨u, hu⟩) nxy nxz nxu
        nyz nyu nzu _ _ k hk]
    simp only [eq_mul8, Fin.getElem_fin]
    by_cases ey : y = k
    · subst ey; simp only [Ne.symm nyu, Ne.symm nyz, ite_true, ite_false]
    by_cases ez : z = k
    · subst ez; simp only [ey, Ne.symm nzu, ite_true, ite_false]
    by_cases eu : u = k
    · subst eu; simp only [ey, ez, ite_true, ite_false]
    by_cases ex : x = k
    · subst ex; simp only [ey, ez, eu, ite_true, ite_false]
    simp only [ey, ez, eu, ex, ite_false]
  · rw [w.mem, gMem]
    have m := List.mem_singleton_self (⟨State.addr V, 128⟩ : Region)
    exact frame_write64 (frame_write64 (frame_write64 (frame_write64 h.frame m fitV (by omega) _) m fitV
      (by omega) _) m fitV (by omega) _) m fitV (by omega) _

theorem round_ok (r : Nat) {V Bk : BitVec 32} {M : Block 64} {s₀ s : State} {v : Work 64}
    (c : RCtx V Bk M s₀) (h : RI V s₀ v s) :
    WP isa (round r) s (RI V s₀ (Spec.Blake2.round Spec.Blake2.b M v r)) := by
  unfold round
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 4) (z := 8) (u := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 0 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 5) (z := 9) (u := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 1 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 6) (z := 10) (u := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 2 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 3) (y := 7) (z := 11) (u := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 3 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 5) (z := 10) (u := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 4 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 6) (z := 11) (u := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 5 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 7) (z := 8) (u := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 6 c h) fun s h => ?_)
  refine WP.mono (gAt_ok (x := 3) (y := 4) (z := 9) (u := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 7 c h) fun s h => ?_
  exact h

theorem rounds_ok {V Bk : BitVec 32} {M : Block 64} {s₀ : State} {v : Work 64} (c : RCtx V Bk M s₀)
    (hv : ∀ k (hk : k < 16), rd64 s₀.mem V (8 * k) = v[k]) (n : Nat) :
    WP isa (rounds n) s₀ (RI V s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.b M) v)) := by
  induction n with
  | zero => exact WP.block_nil ⟨hv, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok n c hs

end VG.Proof.Blake2.ArmB
