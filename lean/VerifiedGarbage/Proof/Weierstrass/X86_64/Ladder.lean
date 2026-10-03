import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks

/-!
# Short Weierstrass curves on x86-64: the ladder

An iteration of `ladder L` computes `D = R + R` and `T = D + G` with the
complete addition (`rcb_ok`), and selects `T` into `R` if the scalar's bit
is set, else `D` (`ladderBody_ok`), for the scalar `k` whose bits are the
table at `L.bits`. `ladder_ok` takes the loop's invariant `Q j` on what `R`
holds, and that an iteration keeps it (`Step`): the callers' invariant is
that `R` represents `[k >>> j]P` (`step_rep`, in `Rep.lean`), and only they
need the group law and the algebra it is proven with.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The slots of the ladder. -/
def ladSlots (L : LadderCfg) : List Nat :=
  [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z] ++ rcbW L.S L.D ++ [L.T.x, L.T.y, L.T.z]

/-- The slots the ladder writes. -/
def ladWs (L : LadderCfg) : List Nat := [L.R.x, L.R.y, L.R.z] ++ rcbW L.S L.D ++ rcbW L.S L.T

/-- What the ladder writes: its slots and the modulus's temporary area. -/
def ladW (L : LadderCfg) : List (Nat × Nat) :=
  (ladWs L).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)]

/-- The slots it reads only: the curve's `a` and `3b`, and `G`. -/
def ladRo (L : LadderCfg) : List Nat := [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z]

/-- What an iteration reads: those and `R`. -/
def ladR (L : LadderCfg) : List Nat := ladRo L ++ [L.R.x, L.R.y, L.R.z]

/-- The ladder's slots are in the working space and apart (`lay`), the two
additions write slots apart from what they read (`a1`, `a2`), the slots read
only are not written (`ro`), `R`'s are not `D`'s or `T`'s, and the table of
bits is apart from what is written. -/
structure LadLay (L : LadderCfg) (size : Nat) : Prop where
  lay : Lay L.M size (· ∈ ladSlots L)
  a1 : RcbApart L.S L.R L.R L.D
  a2 : RcbApart L.S L.D L.G L.T
  ro : ∀ x ∈ ladRo L, x ∉ ladWs L
  rne : L.R.x ≠ L.R.y ∧ L.R.x ≠ L.R.z ∧ L.R.y ≠ L.R.z
  rdt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], x ∉ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z]
  nbits : 1 ≤ L.nbits ∧ L.nbits < 2 ^ 31
  bits : L.bits + L.nbits ≤ size
  bits_w : ∀ w ∈ ladW L, L.bits + L.nbits ≤ w.1 ∨ w.1 + w.2 ≤ L.bits

theorem ladWs_slots (L : LadderCfg) : ∀ x ∈ ladWs L, x ∈ ladSlots L := by
  intro x hx
  simp only [ladWs, ladSlots, rcbW, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  grind

theorem ladR_slots (L : LadderCfg) : ∀ x ∈ ladR L, x ∈ ladSlots L := by
  intro x hx
  simp only [ladR, ladRo, ladSlots, rcbW, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  grind

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLay.apart_w {L : LadderCfg} {size : Nat} (hL : LadLay L size) {x : Nat}
    (hx : x ∈ ladSlots L) (hxw : x ∉ ladWs L) :
    ∀ w ∈ ladW L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hx (ladWs_slots L y hy) fun h => hxw (h ▸ hy)
  · exact hL.lay.tmp x hx

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them. -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z X Y Z =
      (X2, Y2, Z2) →
    VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- The loop's invariant at `rbx = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (C : Curve) (base : Addr) (size : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob L.M.n) s₀ s
  unch : Unch base (ladW L) s₀.mem s.mem
  mod : ModOk L.M size C.p s.mem base
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

theorem mem_ladRo_ladR {L : LadderCfg} {x : Nat} (h : x ∈ ladRo L) : x ∈ ladR L :=
  List.mem_append_left _ h

/-- `∀ x ∈ l₁, x ∈ l₂` for lists written out. -/
macro "sub_list" : tactic => `(tactic| (show (_ : List Nat) ⊆ _; simp only [List.cons_subset,
  List.nil_subset, List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true,
  and_true, and_self, ladR, ladRo, ladSlots, ladWs, rcbW, rcbR, List.cons_append, List.nil_append]))

/-- `x ∈ l` for a list written out. -/
macro "mem_list" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, ladR, ladRo, ladSlots, ladWs, rcbW, rcbR, List.cons_append,
  List.nil_append]))

theorem mem_ladW_D {L : LadderCfg} : ∀ w ∈ (rcbW L.S L.D).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)],
    w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | hw
  · exact Or.inl ⟨y, by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr hy), rfl⟩
  · exact Or.inr hw

theorem mem_ladW_T {L : LadderCfg} : ∀ w ∈ (rcbW L.S L.T).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)],
    w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | hw
  · exact Or.inl ⟨y, by simp only [ladWs, List.mem_append]; exact Or.inr hy, rfl⟩
  · exact Or.inr hw

theorem mem_ladW_R {L : LadderCfg} :
    ∀ w ∈ [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)], w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map]
  refine Or.inl ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨L.R.x, by simp [ladWs], rfl⟩
  · exact ⟨L.R.y, by simp [ladWs], rfl⟩
  · exact ⟨L.R.z, by simp [ladWs], rfl⟩

theorem ladR_V₁ (L : LadderCfg) : ∀ x ∈ rcbR L.S L.R L.R, x ∈ ladR L := by sub_list

theorem ladR_S₁ (L : LadderCfg) : ∀ x ∈ rcbW L.S L.D ++ rcbR L.S L.R L.R, x ∈ ladSlots L := by
  sub_list

theorem ladR_V₂ (L : LadderCfg) : ∀ x ∈ rcbR L.S L.D L.G, x ∈ rcbW L.S L.D ++ ladR L := by sub_list

theorem ladR_S₂ (L : LadderCfg) : ∀ x ∈ rcbW L.S L.T ++ rcbR L.S L.D L.G, x ∈ ladSlots L := by
  sub_list

theorem ladPts_slots (L : LadderCfg) :
    ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ∈ ladSlots L := by
  sub_list

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (C : Curve) (base : Addr) (size : Nat) (E : Nat → Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOk L.M size C.p s'.mem base
  gpr : ∀ r, r ∉ clob L.M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (ladW L) s.mem s'.mem
  lt : ∀ x ∈ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], wordsVal s'.mem base x L.M.n < C.p
  vals : ∃ X2 Y2 Z2 X3 Y3 Z3 : Fe C,
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z) (E L.R.x)
      (E L.R.y) (E L.R.z) = (X2, Y2, Z2) ∧
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) X2 Y2 Z2 (E L.G.x) (E L.G.y) (E L.G.z) =
      (X3, Y3, Z3) ∧
    tmv C L.M.n base s' L.D.x = X2 ∧ tmv C L.M.n base s' L.D.y = Y2 ∧
    tmv C L.M.n base s' L.D.z = Z2 ∧ tmv C L.M.n base s' L.T.x = X3 ∧
    tmv C L.M.n base s' L.T.y = Y3 ∧ tmv C L.M.n base s' L.T.z = Z3

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {C : Curve} {base : Addr} {size : Nat} (hL : LadLay L size)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M base size C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L C base size E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprogB L.M (rcb L.S L.R L.R L.D)) (.seq (fprogB L.M (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono (rcb_ok hL.lay hp hL.a1 (ladR_S₁ L) hI (ladR_V₁ L))
    fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_))
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono (rcb_ok hL.lay hp hL.a2 (ladR_S₂ L) I₂ (ladR_V₂ L))
    fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_))
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨k₃.scr (k₂.scr hI.scr), I₃.mod, fun r hr => (k₃.gpr r hr).trans (k₂.gpr r hr),
    k₃.rd.trans k₂.rd, k₃.wr.trans k₂.wr, (k₂.unch.trans k₃.unch).mono fun w hw => ?_,
    fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact mem_ladW_D w hw
    · exact mem_ladW_T w hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact I₃.lt x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> mem_list)
  · refine ⟨_, _, _, _, _, _, t₂.symm, ?_, (I₃.val L.D.x (hD L.D.x (by simp))).trans (n₃ L.D.x (hDT L.D.x (by simp))),
      (I₃.val L.D.y (hD L.D.y (by simp))).trans (n₃ L.D.y (hDT L.D.y (by simp))),
      (I₃.val L.D.z (hD L.D.z (by simp))).trans (n₃ L.D.z (hDT L.D.z (by simp))),
      I₃.val L.T.x (hT L.T.x (by simp)), I₃.val L.T.y (hT L.T.y (by simp)),
      I₃.val L.T.z (hT L.T.z (by simp))⟩
    rw [← n₂ L.S.a (hro L.S.a (by simp [ladRo])), ← n₂ L.S.b3 (hro L.S.b3 (by simp [ladRo])),
      ← n₂ L.G.x (hro L.G.x (by simp [ladRo])), ← n₂ L.G.y (hro L.G.y (by simp [ladRo])),
      ← n₂ L.G.z (hro L.G.z (by simp [ladRo]))]
    exact t₃.symm

/-- The mask of the bit, `R = D` or `T` by it, and `test rbx, rbx`. -/
theorem ladSel_ok {L : LadderCfg} {base : Addr} {size : Nat} (hL : LadLay L size) {s : State}
    (hs : Scr s base size) {t : Nat} (ht : t < L.nbits) (hrbx : s.gpr .rbx = BitVec.ofNat 64 t)
    {c : Bool} (hc : s.mem (off base (L.bits + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T ++
      ([.alu .test .rbx (.reg .rbx)] : List Instr))) s
      fun s' => Scr s' base size ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧
        s'.zf = some (decide (t = 0)) ∧ KeepRegs [.rax, .rcx, .rdx] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hnb := hL.nbits
  have hbl := hL.bits
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok hs hrbx (by omega) hc) fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ := hs.of_keeps k₄ (by decide)
  have hm₄ : s₄.mem = s.mem := k₄.2.1
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  refine WP.mono (selPt_ok hs₄ c c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.lay.le d (ladPts_slots L d hd))
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have hrbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k₅.gpr _ (by decide), k₄.1 _ (by decide), hrbx]
  refine WP.mono (testRbx_ok s₅ (by omega) hrbx₅) fun s₆ ⟨z₆, k₆⟩ => ?_
  have hm₆ : s₆.mem = s₅.mem := k₆.2.1
  refine ⟨hs₅.of_keeps k₆ (by decide), by rw [k₆.1 .rbx (by decide), hrbx₅], z₆,
    ((Keeps.regs k₄).mono (by sub_regs)).trans ((k₅.mono (by sub_regs)).trans
      ((Keeps.regs k₆).mono (by intro q hq; cases hq))),
    fun x hx => by
      rw [hm₆, O₅ x (hx (L.R.x, 8 * L.M.n) (by simp)) (hx (L.R.y, 8 * L.M.n) (by simp))
        (hx (L.R.z, 8 * L.M.n) (by simp)), hm₄],
    by rw [hm₆, ex₅, hm₄], by rw [hm₆, ey₅, hm₄], by rw [hm₆, ez₅, hm₄]⟩

/-- An iteration. -/
theorem ladderBody_ok {L : LadderCfg} {C : Curve} {base : Addr} {size k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hL : LadLay L size) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L C base size Q s₀ s j) :
    WP isa (ladderBody L) s fun s' =>
      LadInv L C base size Q s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_w (ladR_slots L x (mem_ladRo_ladR hx)) (hL.ro x hx))
      (by have := hL.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); omega)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `sub rbx, 1`.
  rw [ladderBody]
  refine WP.seq (WP.mono (decRbx_ok s hj (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have I₁ : Inv L.M base size C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.scr.of_keeps k₁ (by decide), hm₁ ▸ hI.mod, ladR_slots L, fun x hx => ?_,
      fun x _ => by rw [tmv, hm₁]⟩
    rw [hm₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladW L) s₀.mem s₃.mem := by
    refine (hI.unch.trans (by rw [← hm₁]; exact A.unch)).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₃.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    have hbl := hL.bits
    rw [hU₃.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega), hbits _ (by omega)]
  have hrbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [A.gpr _ (rbx_not_clob _), b₁]
  have hstep := hstep (j - 1) (by omega) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  refine WP.mono (ladSel_ok hL A.scr (by omega) hrbx₃ hbyte)
    fun s' ⟨hs', b', z', k', U', ex, ey, ez⟩ => ⟨⟨hs', b', ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, z'⟩
  · have hr' : r ∉ clob L.M.n := fun h => hr (List.mem_cons_of_mem _ h)
    have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self ..)
    have hra : r ≠ .rax := fun h => hr' (h ▸ by simp [clob])
    have hrc : r ≠ .rcx := fun h => hr' (h ▸ by simp [clob])
    have hrd : r ≠ .rdx := fun h => hr' (h ▸ by simp [clob])
    rw [k'.gpr r (by simp [hra, hrc, hrd]), A.gpr r hr', k₁.1 r (by simp [hrb]), hI.keep.gpr r hr]
  · rw [k'.rd, A.rd, k₁.2.2.1, hI.keep.rd]
  · rw [k'.wr, A.wr, k₁.2.2.2, hI.keep.wr]
  · exact (hU₃.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact mem_ladW_R w hw
  · have hM := A.mod
    have hmo := hL.lay.mo
    have hle := hL.lay.le
    refine ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, ?_, hM.inv⟩
    rw [U'.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hmo L.R.x (ladPts_slots L _ (by simp))).symm
      · exact (hmo L.R.y (ladPts_slots L _ (by simp))).symm
      · exact (hmo L.R.z (ladPts_slots L _ (by simp))).symm) (by have := A.scr.nowrap; have := hM.mo; omega)]
    exact hM.val
  · have hlt := A.lt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [ex]; split
      · exact hlt.2.2.2.1
      · exact hlt.1
    · rw [ey]; split
      · exact hlt.2.2.2.2.1
      · exact hlt.2.1
    · rw [ez]; split
      · exact hlt.2.2.2.2.2
      · exact hlt.2.2.1
  · have hx : tmv C L.M.n base s' L.R.x = if k.testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s' L.R.y = if k.testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s' L.R.z = if k.testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladW` change. -/
theorem ladder_ok {L : LadderCfg} {C : Curve} {base : Addr} {size k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hL : LadLay L size) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOk L.M size C.p s.mem base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder L) s fun s' => KeepRegs (powClob L.M.n) s s' ∧ Unch base (ladW L) s.mem s'.mem ∧
      ModOk L.M size C.p s'.mem base ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.nbits
  rw [ladder]
  refine WP.seq (WP.mono (mov32Rbx_ok s hnb.2) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine countLoop_ok (Inv := fun j s' => LadInv L C base size Q s s' j) (n := L.nbits)
    (fun j s' h1 h2 hi => ladderBody_ok hL hp (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, hi.q⟩)
    hnb.1 ?_
  refine ⟨hs.of_keeps k₁ (by decide), b₁, ⟨fun r hr => k₁.1 r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; simp [h, powClob]),
    k₁.2.2.1, k₁.2.2.2⟩, by rw [hm₁]; exact Unch.refl _ _ _, hm₁ ▸ hM,
    fun x hx => by rw [hm₁]; exact hlt x (List.mem_append_right _ hx), ?_⟩
  simp only [tmv, hm₁]
  exact hR

end VG.Proof.Weierstrass.X86_64
