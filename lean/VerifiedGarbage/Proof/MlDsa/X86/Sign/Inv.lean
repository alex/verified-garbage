import VerifiedGarbage.Proof.MlDsa.X86.Sign.Blocks

/-!
# ML-DSA signing on x86 (32-bit): what the pieces keep

Untrusted: everything here is checked by Lean. The slots of polynomials
(`nS` of them, `slot_okW`), families of consecutive slots (`Fam`), and what
a piece that writes the buffers `bs` keeps: the frame of each call is
widened to a few large buffers (`frIn`), so that what a whole phase keeps is
shown once (`Fam.keep`, `keepB`, `keepW'`). The tactic `ofs` proves the
arithmetic of offsets from the facts of `PS p`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem.X86 (sub_of_contains contains_at)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The slot of `Â[0, 0]`. -/
abbrev aBase (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- The number of slots of polynomials. -/
abbrev nS (p : Params) : Nat := 5 + 4 * p.k + 3 * p.ℓ + p.k * p.ℓ

variable {p : Params}

/-! ## Buffers within buffers -/

/-- `c` lies within `d`. -/
def In (c d : Buf) : Prop := c.arg = d.arg ∧ d.off ≤ c.off ∧ c.off + c.len ≤ d.off + d.len

theorem rgn_sub {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {c d : Buf} (hc : Y.ok c = true) (hd : Y.ok d = true)
    (h : In c d) : Region.Sub (c.rgn s₀) (d.rgn s₀) := by
  obtain ⟨e, h₁, h₂⟩ := h
  show Region.Sub ⟨c.addr s₀, c.len⟩ ⟨d.addr s₀, d.len⟩
  have ea : c.addr s₀ = (d.ptr s₀).setWidth 64 + BitVec.ofNat 64 (c.off - d.off) := by
    show c.addr s₀ = d.addr s₀ + _
    rw [Buf.addr_eq hp hc, Buf.addr_eq hp hd, BitVec.add_assoc, ← BitVec.ofNat_add, e,
      show d.off + (c.off - d.off) = c.off by omega]
  rw [ea]
  exact sub_of_contains (contains_at (by omega) (Buf.fit hp hd))

/-- The frame of a piece, widened to the buffers `ds`. -/
theorem frIn {s₀ : State} (hp : TPre (Y p) s₀) {bs ds : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    (h : ∀ c ∈ bs, (Y p).ok c = true ∧ ∃ d ∈ ds, (Y p).ok d = true ∧ In c d) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ ds M) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hc', d, hd, hd', i⟩ := h c hc
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hd), rgn_sub hp hc' hd' i⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp hNM (by show M + 16 ≤ 96; omega)⟩

theorem Frame.trans' {rs : List Region} {m₁ m₂ m₃ : Mem} (h₁ : Frame rs m₁ m₂) (h₂ : Frame rs m₂ m₃) :
    Frame rs m₁ m₃ := h₁.trans h₂

/-! ## Families of slots -/

/-- The `n` slots from `b` hold `f 0, …, f (n - 1)`. -/
def Fam (s₀ : State) (m : Mem) (b n : Nat) (f : Nat → Poly) : Prop :=
  ∀ j < n, PolyIs m (Buf.addr s₀ (pS (b + j))) (f j)

theorem Fam.congr {s₀ : State} {m : Mem} {b n : Nat} {f g : Nat → Poly} (h : Fam s₀ m b n f)
    (e : ∀ j < n, f j = g j) : Fam s₀ m b n g := fun j hj => e j hj ▸ h j hj

/-- A buffer of `scratch` apart from `[lo, hi)`, or not in `scratch`. -/
def Out (p : Params) (lo hi : Nat) (c : Buf) : Prop :=
  (Y p).ok c = true ∧ (c.arg = SC → c.off + c.len ≤ lo ∨ hi ≤ c.off)

/-- The slots of `y`, `ŷ` and `w`. -/
abbrev yB (p : Params) : Nat := 5 + p.k
abbrev yhB (p : Params) : Nat := 5 + p.k + p.ℓ
abbrev wB (p : Params) : Nat := 5 + p.k + 2 * p.ℓ

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1B (p : Params) : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2B (p : Params) : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0B (p : Params) : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- A write apart from all of the families. -/
def OutK (p : Params) (n1 n2 n0 : Nat) (c : Buf) : Prop :=
  Out p (oP (aBase p)) (oP (nS p)) c ∧ Out p (oP (s1B p)) (oP (s1B p + n1)) c ∧
    Out p (oP (s2B p)) (oP (s2B p + n2)) c ∧ Out p (oP (t0B p)) (oP (t0B p + n0)) c

/-- A write that an iteration of the loop may do: apart from `Â`, `ŝ₁`,
`ŝ₂`, `t̂₀`, `CNT`, `KAP` and `ρ″`. -/
def OutI (p : Params) (c : Buf) : Prop :=
  OutK p p.ℓ p.k p.k c ∧ Out p oCNT (oKAP + 4) c ∧ Out p oMS (oMS + 64) c

theorem PS.w1pos {p : Params} (ps : PS p) : 0 < p.k * w1Len p :=
  Nat.mul_pos (by have := ps.hk; omega) (by rcases ps.hw1Len with h | h <;> omega)

/-- The facts of `PS p` that the offsets need, in the context. -/
macro "ofs" : tactic => do
  let ps := Lean.mkIdent `ps
  `(tactic| (
  have _ := ($ps).hk; have _ := ($ps).hl; have _ := ($ps).hscr; have _ := ($ps).hsigLen; have _ := ($ps).hskLen
  have _ := ($ps).hcLen; have _ := ($ps).hzLen; have _ := ($ps).hw1; have _ := ($ps).hω; have _ := PS.w1pos $ps
  try simp only [nS, aBase, s1B, s2B, t0B, yB, yhB, wB] at *
  set_option linter.unusedSimpArgs false in
  simp only [Lay.apart, Lay.okW_iff, Lay.ok_iff, Lay.sep_iff, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    true_and, ne_eq, not_true_eq_false, false_and, or_false, true_or, or_true, Out, In,
    Y_n, Y_alen0, Y_alen1, Y_alen2, Y_alen3, Y_alen4, Y_awr0, Y_awr1, Y_awr2, Y_awr3, Y_awr4,
    oP, SC, oPS, oRS, oHIN, oMS, oCT, oW1, oST, oWK, oOK, oCNT, oKAP, oONES, skS1, skS2, skT0, sigZ, sigH, aBase, s1B, s2B, t0B, OutK, OutI, yB, yhB, wB, bMu, bRnd, bSk, bSig]
  omega))

/-! ## Slots -/

section
variable (ps : PS p)
include ps

theorem slot_ok {j : Nat} (hj : j < nS p) : (Y p).okW (pS j) = true := by ofs
theorem slot_ok' {j : Nat} (hj : j < nS p) : (Y p).ok (pS j) = true := (Lay.okW_iff.mp (slot_ok ps hj)).1

omit ps in
theorem slot_sep {i j : Nat} (h : i ≠ j) : (Y p).sep (pS i) (pS j) = true := by
  simp only [Lay.sep_iff, oP, true_and, ne_eq, not_true_eq_false, false_and, or_false]; omega

omit ps in
/-- An entry of `Â` is a slot. -/
theorem aP_eq {i j : Nat} : aP p i j = pS (5 + 4 * p.k + 3 * p.ℓ + (p.ℓ * i + j)) := by
  simp only [aP, Nat.add_assoc]

omit ps in
theorem aIdx {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have : p.ℓ * i + p.ℓ ≤ p.ℓ * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Nat.mul_comm p.k]; omega

end

theorem apart_of {b : Buf} (hb : (Y p).ok b = true) (hbs : b.arg = SC) {bs : List Buf}
    (h : ∀ c ∈ bs, Out p b.off (b.off + b.len) c) : (Y p).apart b bs = true := by
  simp only [Lay.apart, hb, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
  intro c hc
  obtain ⟨hc₁, hc₂⟩ := h c hc
  refine ⟨hc₁, Lay.sep_iff.mpr ?_⟩
  by_cases e : b.arg = c.arg
  · exact .inl ⟨e, (hc₂ (e ▸ hbs)).symm⟩
  · exact .inr ⟨e, .inl (by rw [hbs]; rfl)⟩

theorem Fam.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n : Nat} (hb : b + n ≤ nS p)
    (h : ∀ c ∈ bs, Out p (oP b) (oP (b + n)) c) {f : Nat → Poly} (hf : Fam s₀ m b n f) : Fam s₀ m' b n f :=
  fun j hj => polyIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega)
    (apart_of (slot_ok' ps (Nat.lt_of_lt_of_le (by omega : b + j < b + n) hb)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [oP] at h₂ ⊢; have := h₂ e; omega⟩) fr) (hf j hj)

theorem keepB {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (hc : (Y p).ok (sc o l) = true)
    (h : ∀ c ∈ bs, Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o l)) l = bytesAt m (Buf.addr s₀ (sc o l)) l :=
  keepBytes hp (N := N) (by show N + 16 ≤ 96; omega) (apart_of hc rfl h) fr

theorem keepW' {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o : Nat} (hc : (Y p).ok (sc o 4) = true)
    (h : ∀ c ∈ bs, Out p o (o + 4) c) : m'.readW (Buf.addr s₀ (sc o 4)) 32 = m.readW (Buf.addr s₀ (sc o 4)) 32 :=
  keepW hp (N := N) (by show N + 16 ≤ 96; omega) (apart_of hc rfl h) fr

theorem keepP {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {j : Nat} (hj : j < nS p)
    (h : ∀ c ∈ bs, Out p (oP j) (oP (j + 1)) c) {f : Poly} (hf : PolyIs m (Buf.addr s₀ (pS j)) f) :
    PolyIs m' (Buf.addr s₀ (pS j)) f := by
  have := Fam.keep hp ps hN fr (b := j) (n := 1) (by omega) h (f := fun _ => f) fun i hi => by
    rw [show i = 0 by omega]; exact hf
  exact this 0 (by decide)

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.snoc {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → Poly} (h : Fam s₀ m b n f)
    (h' : PolyIs m (Buf.addr s₀ (pS (b + n))) (f n)) : Fam s₀ m b (n + 1) f := fun j hj => by
  by_cases e : j < n
  · exact h j e
  · rw [show j = n by omega]; exact h'

end VG.Proof.MlDsa.X86.Sign
