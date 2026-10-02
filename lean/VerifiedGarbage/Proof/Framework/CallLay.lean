import VerifiedGarbage.Proof.Framework.Offset

/-!
# The buffers of a function that calls others

A function that is a sequence of calls on buffers (its arguments and its
working space) keeps the address of each buffer in a register its callees
preserve. A layout lists these registers with the lengths of their buffers,
read (`rbs`) or written (`wbs`); a pointer is a register and an offset into
its buffer, at `addr g p` for the registers' contents `g`.

Whether a pointer lies within its buffer (`inB`), whether two lie apart
(`sepB`: in different buffers, one of them written (`w`), or apart within
the same buffer), and whether a region is kept by code that writes others
(`keepB`) are checked by evaluation. `Lay` says the buffers are where the
layout says: small, apart from each other where one is written and from the
stack the calls use (`sr`), not wrapping around, and permitted. The facts a
callee's contract needs then follow from the checks (`Lay.disj`, `Lay.stkD`,
`Lay.nwp`, `Lay.inR`, `Lay.inW`), as do the regions a piece of code keeps
(`Lay.fdisj`).

All of this is generic in the registers `R` and in how a state gives their
contents: each target instantiates it with its own state, adding what its
calls need besides (see `Proof/MlDsa/AArch64/Call/Base.lean`).
-/

namespace VG.CallLay

variable {R : Type} [DecidableEq R]

/-- The address of the pointer `p`, for the contents `g` of the registers. -/
abbrev addr (g : R → Addr) (p : R × Nat) : Addr := g p.1 + BitVec.ofNat 64 p.2

/-- The region of `x.2` bytes at the pointer `x.1`. -/
abbrev toR (g : R → Addr) (x : (R × Nat) × Nat) : Region := ⟨addr g x.1, x.2⟩

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (R × Nat)) (p : R × Nat) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- Whether the buffer of `r` is among the written ones, `wbs`. -/
def isW (wbs : List (R × Nat)) (r : R) : Bool := (wbs.lookup r).isSome

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written (`w`), or in the same buffer. -/
def sepB (w : R → Bool) (bs : List (R × Nat)) (p : R × Nat) (l : Nat) (q : R × Nat) (k : Nat) : Bool :=
  inB bs p l && inB bs q k &&
    ((p.1 != q.1 && (w p.1 || w q.1)) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one code keeps (`kp`). -/
def keepB (kp w : R → Bool) (bs : List (R × Nat)) (ws : List ((R × Nat) × Nat)) (p : R × Nat) (l : Nat) : Bool :=
  kp p.1 && inB bs p l && ws.all fun x => sepB w bs p l x.1 x.2

theorem lookup_mem : ∀ {bs : List (R × Nat)} {r : R} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem inB_spec {bs : List (R × Nat)} {p : R × Nat} {l : Nat} (h : inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold inB at h
  split at h
  · rename_i n hn; exact ⟨n, lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {w : R → Bool} {bs : List (R × Nat)} {p q : R × Nat} {l k : Nat} (h : sepB w bs p l q k = true) :
    inB bs p l = true ∧ inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (w p.1 || w q.1) = true) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  rcases h.2 with h | h
  · exact .inl ⟨h.1, by simpa [Bool.or_eq_true] using h.2⟩
  · exact .inr h

/-- Two pointers into the same buffer are apart if their offsets are. -/
theorem sepB_same (w : R → Bool) (bs : List (R × Nat)) (r : R) (o l o' l' : Nat) :
    sepB w bs (r, o) l (r, o') l' =
      (inB bs (r, o) l && inB bs (r, o') l' && (decide (o + l ≤ o') || decide (o' + l' ≤ o))) := by
  simp [sepB]

/-- Two pointers into different buffers, one of them written, are apart. -/
theorem sepB_ne {w : R → Bool} (bs : List (R × Nat)) {r r' : R} (h : r ≠ r') (hw : (w r || w r') = true)
    (o l o' l' : Nat) : sepB w bs (r, o) l (r', o') l' = (inB bs (r, o) l && inB bs (r', o') l') := by
  simp only [sepB, bne_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h, hw, Bool.false_and, Bool.or_false, Bool.and_true]

section
variable {kp w : R → Bool} {bs : List (R × Nat)} {ws : List ((R × Nat) × Nat)} {p : R × Nat} {l : Nat}

theorem keepB_kp (hc : keepB kp w bs ws p l = true) : kp p.1 = true := by
  simp only [keepB, Bool.and_eq_true] at hc
  exact hc.1.1

theorem keepB_in (hc : keepB kp w bs ws p l = true) : inB bs p l = true := by
  simp only [keepB, Bool.and_eq_true] at hc
  exact hc.1.2

theorem keepB_sep (hc : keepB kp w bs ws p l = true) : ∀ x ∈ ws, sepB w bs p l x.1 x.2 = true := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at hc
  exact hc.2

end

/-! ## Parts of buffers -/

theorem inB_sub {bs : List (R × Nat)} {r : R} {o L o' l : Nat} (h : inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : inB bs (r, o') l = true := by
  unfold inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega
  · cases h

theorem sepB_sub {w : R → Bool} {bs : List (R × Nat)} {r : R} {o L o' l : Nat} {q : R × Nat} {k : Nat}
    (h : sepB w bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : sepB w bs (r, o') l q k = true := by
  unfold sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega⟩

theorem keepB_sub {kp w : R → Bool} {bs : List (R × Nat)} {ws : List ((R × Nat) × Nat)} {r : R} {o L o' l : Nat}
    (h : keepB kp w bs ws (r, o) L = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : keepB kp w bs ws (r, o') l = true := by
  unfold keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, inB_sub h.1.2 h2⟩, fun x hx => sepB_sub (h.2 x hx) h1 h2⟩

theorem sub_of_inB {g : R → Addr} {bs : List (R × Nat)} {p : R × Nat} {l : Nat} (h : inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ Region.Sub ⟨addr g p, l⟩ ⟨g p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := inB_spec h
  exact ⟨n, hm, Offset.sub_base _ hl⟩

/-! ## Regions -/

theorem contains_trans {r : Region} {a : Addr} {n off l : Nat} (h : r.Contains a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : r.Contains (a + BitVec.ofNat 64 off) l := by
  simp only [Region.Contains] at h ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_trans hc hl hn⟩

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses `g`
gives their registers: small, apart from each other where one of them is
written (`w`) and from the stack `sr`, not wrapping around, readable (in
`rs ++ ws`) and, for `wbs`, writable (in `ws`). -/
structure Lay (w : R → Bool) (g : R → Addr) (rs ws : List Region) (sr : Region) (rbs wbs : List (R × Nat)) :
    Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (w b.1 || w b'.1) = true →
    Region.Disjoint ⟨g b.1, b.2⟩ ⟨g b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, sr.Disjoint ⟨g b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (g b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (rs ++ ws) (g b.1) b.2
  wr : ∀ b ∈ wbs, InRegions ws (g b.1) b.2

section
variable {w : R → Bool} {g : R → Addr} {rs ws : List Region} {sr : Region} {rbs wbs : List (R × Nat)}
  (L : Lay w g rs ws sr rbs wbs)
include L

theorem Lay.disj {p q : R × Nat} {l k : Nat} (h : sepB w (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨addr g p, l⟩ ⟨addr g q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := sepB_spec h
  obtain ⟨n, hn, hl⟩ := inB_spec hp
  obtain ⟨m, hm, hk⟩ := inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (Offset.sub_base _ hl)).sub_right (Offset.sub_base _ hk)
  · show Region.Disjoint ⟨g p.1 + _, l⟩ ⟨g q.1 + _, k⟩
    rw [← e]
    exact Offset.disjoint _ hs (by simp only at sn; omega) (by simp only at sm; omega)

theorem Lay.stkD {p : R × Nat} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : sr.Disjoint ⟨addr g p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := sub_of_inB (g := g) h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.nwp {p : R × Nat} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (addr g p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((g p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.inR {p : R × Nat} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : InRegions (rs ++ ws) (addr g p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; simp only at this; omega)

theorem Lay.inW {p : R × Nat} {l : Nat} (h : inB wbs p l = true) : InRegions ws (addr g p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.wr (p.1, n) hn) hl
    (by have := L.small _ (List.mem_append_right _ hn); simp only at this; omega)

/-- The region of a check `keepB` is apart from the regions `xs` written and the stack. -/
theorem Lay.fdisj {kp : R → Bool} {xs : List ((R × Nat) × Nat)} {p : R × Nat} {l : Nat}
    (hc : keepB kp w (rbs ++ wbs) xs p l = true) :
    ∀ r ∈ xs.map (toR g) ++ [sr], Region.Disjoint ⟨addr g p, l⟩ r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact L.disj (keepB_sep hc x hx)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD (keepB_in hc)).symm

omit [DecidableEq R] in
/-- A layout holds in a state whose registers of the layout hold the same addresses. -/
theorem Lay.congr {g' : R → Addr} (e : ∀ b ∈ rbs ++ wbs, g' b.1 = g b.1) : Lay w g' rs ws sr rbs wbs := by
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb)]; exact L.wr b hb

end

end VG.CallLay
