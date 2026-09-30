import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Base
import VerifiedGarbage.Proof.MlKem.Arm.Prf

/-!
# ML-DSA on 32-bit ARM: the buffers of the top-level functions

Untrusted: everything here is checked by Lean. The top-level functions work
on five buffers (a `Lay`, as ML-KEM's): `scratch` (buffer 0), the `STK`
bytes of stack below the stack pointer (buffer 1), and their arguments
(buffers 2, 3 and 4, whose pointers they keep in `r4`, `r5` and `r6`; `r7`
holds `scratch`): `ix` maps each register to the buffer it points into. A
state where they run their parts is a `Site`.

A pointer `q` (a register and an offset) is the address `lpa L q`, and the
region of `l` bytes there the triple `tri q l`, so that what a part writes
and what the proofs keep track of are lists of triples (`Kept`, `sepB`, as
in ML-KEM). The sponge (`hash`) is ML-KEM's (`hash_ok`, `hash_ct`), which
use the 8 bytes below the stack pointer as buffer 1: `hashLay` is the layout
with buffer 1 so narrowed (`hashS`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.Sha3 (bytesAt)

/-- The buffer each register points into. -/
def ix : Reg → Nat
  | .r7 => 0
  | .r4 => 2
  | .r5 => 3
  | .r6 => 4
  | _ => 5

/-- The `l` bytes at the pointer `q`. -/
abbrev tri (q : Ptr) (l : Nat) : Nat × Nat × Nat := (ix q.1, q.2, l)

/-- The address of the pointer `q`. -/
abbrev lpa (L : Lay) (q : Ptr) : Addr := L.A (ix q.1) q.2

/-- The buffers fit in the address space, and a buffer of `Wb` (written, or
the stack) is apart from every other: buffers only read may overlap each
other. -/
structure OkW (L : Lay) (Wb : List Nat) : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j → (i ∈ Wb ∨ j ∈ Wb) →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

theorem OkW.ok {L : Lay} {Wb : List Nat} (h : OkW L Wb) (hall : ∀ i < L.sizes.length, i ∈ Wb) : L.Ok :=
  ⟨h.fit, fun i hi j hj hij => h.disj i hi j hj hij (.inl (hall i hi))⟩

/-- Two regions apart, one of them in a buffer of `Wb`, or both in the same. -/
theorem disjW' {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb ∨ i = j) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 32 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega))
  · have hw' : i ∈ Wb ∨ j ∈ Wb := by rcases hw with h | h | h; exacts [.inl h, .inr h, absurd h e]
    exact ((hL.disj _ ha _ hb e hw').sub_left (Lay.R_sub hla)).sub_right (Lay.R_sub hlb)

/-- Two regions apart, one of them in a buffer of `Wb`. -/
theorem disjW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb) :
    (L.R i o l).Disjoint (L.R j o' l') :=
  disjW' hL h (hw.elim .inl fun h => .inr (.inl h))

/-- A state where the parts of a top-level function run, with `STK` bytes of
stack, and the buffers `Wb` written (and the stack). -/
structure Site (L : Lay) (Wb : List Nat) (STK : Nat) (s : State) : Prop where
  ok : OkW L Wb
  len : L.sizes.length = 5
  w0 : 0 ∈ Wb
  w1 : 1 ∈ Wb
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = STK
  p1 : L.ptr 1 = s.sp - BitVec.ofNat 32 STK
  s8 : 8 ≤ STK
  spk : STK ≤ s.sp.toNat
  r7 : s.gpr .r7 = L.ptr 0
  r4 : s.gpr .r4 = L.ptr 2
  r5 : s.gpr .r5 = L.ptr 3
  r6 : s.gpr .r6 = L.ptr 4
  cw : ∀ i ∈ Wb, i ≠ 1 → L.buf i ∈ s.wr
  cr : ∀ i < 5, i ≠ 1 → L.buf i ∈ s.rd ++ s.wr

theorem Site.kept {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) {rs : List Region}
    (hk : Kept rs s s') : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hk.sp]; exact h.p1, h.s8, by rw [hk.sp]; exact h.spk,
    by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.cs .r4 (by decide) (by decide), h.r4],
    by rw [hk.cs .r5 (by decide) (by decide), h.r5], by rw [hk.cs .r6 (by decide) (by decide), h.r6],
    by rw [hk.wr]; exact h.cw, by rw [hk.wr, hk.rd]; exact h.cr⟩

/-- A register of the layout holds the pointer to its buffer. -/
theorem Site.base {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {r : Reg}
    (hr : argOk (.ptr (r, 0)) = true) : s.gpr r = L.ptr (ix r) := by
  simp only [argOk, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((rfl | rfl) | rfl) | rfl
  exacts [h.r4, h.r5, h.r6, h.r7]

/-- A buffer, but the stack, with `l` bytes at offset `o`. -/
def inB (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  w.1 != 1 && w.1 < sz.length && w.2.1 + w.2.2 ≤ sz.getD w.1 0

theorem inB_bounds {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) :
    w.1 ≠ 1 ∧ w.1 < sz.length ∧ w.2.1 + w.2.2 ≤ sz.getD w.1 0 := by
  simp only [inB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem inB_sep {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) {o l : Nat}
    (hs : o + l ≤ sz.getD 1 0) (h1 : 1 < sz.length) : sepB sz w (1, o, l) = true := by
  obtain ⟨h1', h2, h3⟩ := inB_bounds h
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨h2, h1⟩, h3⟩, hs⟩, .inl (.inl h1')⟩

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s)
include h

/-- The value of a pointer argument. -/
theorem Site.val {q : Ptr} (hq : argOk (.ptr q) = true) :
    argVal s (.ptr q) = L.ptr (ix q.1) + BitVec.ofNat 32 q.2 := by
  simp only [argVal, h.base (r := q.1) (by simpa [argOk] using hq)]

/-- The address of a pointer argument into a buffer. -/
theorem Site.addr {q : Ptr} {l : Nat} (hb : inB L.sizes (tri q l) = true) (hl : 0 < l) :
    State.addr (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) = lpa L q ∧
      (L.ptr (ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := by
  obtain ⟨-, h2, h3⟩ := inB_bounds hb
  dsimp only [tri] at h2 h3
  have hf := h.ok.fit _ h2
  simp only [Lay.size] at hf
  refine ⟨addr_add (by omega), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.2) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack below the stack pointer, as buffer 1. -/
theorem Site.belowSub {n : Nat} (hn : n ≤ STK) : Region.Sub (VG.Proof.MlKem.Arm.below s n) (L.R 1 0 STK) := by
  intro x hx
  have e1 := h.p1
  have := h.spk
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 STK)
  simp only [Region.Contains, e1] at hx ⊢
  bv_omega

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem Site.stkD {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) {n : Nat} (hn : n ≤ STK) :
    (L.R w.1 w.2.1 w.2.2).Disjoint (VG.Proof.MlKem.Arm.below s n) := by
  have hsep := inB_sep hb (o := 0) (l := STK) (by rw [← h.sz1]; simp [Lay.size]) (by rw [h.len]; decide)
  exact (disjW h.ok hsep (.inr h.w1)).sub_right (h.belowSub hn)

omit h in
/-- Covers of a buffer the state may write. -/
theorem Site.covW {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) (hw : L.buf w.1 ∈ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] s.wr :=
  Lay.covers hw (inB_bounds hb).2.2

omit h in
/-- Covers of a buffer the state may read. -/
theorem Site.covR {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) (hw : L.buf w.1 ∈ s.rd ++ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] (s.rd ++ s.wr) :=
  Lay.covers hw (inB_bounds hb).2.2

end

/-! ## Changes of the stack -/

/-- What a call changes below the stack pointer is in buffer 1. -/
theorem Site.kept_stk {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) {W : List (Nat × Nat × Nat)}
    {rs : List Region} (hrs : ∀ r ∈ rs, ∃ w ∈ W, Region.Sub r (L.R w.1 w.2.1 w.2.2)) {n : Nat} (hn : n ≤ STK)
    (hk : Kept (rs ++ [VG.Proof.MlKem.Arm.below s n]) s s') : Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  ⟨hk.cs, hk.sp, hk.rd, hk.wr, hk.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, hs⟩ := hrs r hr
      exact ⟨_, List.mem_map.mpr ⟨w, List.mem_append_left _ hw, rfl⟩, hs⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨(1, 0, STK), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩,
        h.belowSub hn⟩⟩

/-! ## The sponge -/

/-- The layout with buffer 1 the 8 bytes below the stack pointer, as ML-KEM's
sponge routine (`hash_ok`) takes it, and of the arguments only those `K`
says (the others empty, so that the buffers are pairwise disjoint). -/
def hashLay (L : Lay) (s : State) (K : Nat → Bool) : Lay :=
  ⟨fun i => if i = 1 then s.sp - BitVec.ofNat 32 8 else L.ptr i,
    [L.size 0, 8, if K 2 then L.size 2 else 0, if K 3 then L.size 3 else 0, if K 4 then L.size 4 else 0]⟩

theorem hashLay_ptr (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) :
    (hashLay L s K).ptr i = L.ptr i := by
  simp only [hashLay, hi, ite_false]

theorem hashLay_R (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (o l : Nat) :
    (hashLay L s K).R i o l = L.R i o l := by
  simp only [Lay.R, hashLay_ptr L s K hi]

theorem hashLay_size_le (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (hi5 : i < 5) :
    (hashLay L s K).size i ≤ L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact Nat.le_refl _
  all_goals (show (if _ then _ else 0) ≤ _; split <;> omega)

theorem hashLay_size (L : Lay) (s : State) {K : Nat → Bool} {i : Nat} (hi : i ≠ 1) (hK : i = 0 ∨ K i = true)
    (hi5 : i < 5) : (hashLay L s K).size i = L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    rcases hK with h | h
    · omega
    · show (if _ then _ else 0) = _; rw [ite_eq_left h]

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {K : Nat → Bool}
  (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
include h hK

theorem hashLay_ok : (hashLay L s K).Ok := by
  have hL := h.ok
  have e8 : (⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ : Region) = VG.Proof.MlKem.Arm.below s 8 := by
    rw [addr_sub (Nat.le_trans h.s8 h.spk)]
  have hsub : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ (L.buf 1) := by
    rw [e8, Lay.buf, show (⟨State.addr (L.ptr 1), L.size 1⟩ : Region) = L.R 1 0 STK by
      rw [h.sz1]; simp only [Lay.R, add_ofNat_zero]]
    exact h.belowSub h.s8
  have hl5 := h.len
  have bi : ∀ k, k < 5 → k ≠ 1 → Region.Sub ⟨State.addr ((hashLay L s K).ptr k), (hashLay L s K).size k⟩
      (L.buf k) := fun k hk hk1 => by
    rw [hashLay_ptr L s K hk1]
    intro x hx
    have := hashLay_size_le L s K hk1 hk
    simp only [Region.Contains] at hx ⊢
    omega
  have b1 : (⟨State.addr ((hashLay L s K).ptr 1), (hashLay L s K).size 1⟩ : Region) =
      ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · simp only [hashLay, List.length_cons, List.length_nil] at hi
    by_cases e : i = 1
    · subst e
      show (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := h.s8; have := h.spk; have := s.sp.isLt; bv_omega
    · have := hashLay_size_le L s K e (by omega)
      simp only [hashLay_ptr L s K e]
      exact Nat.le_trans (Nat.add_le_add_left this _) (hL.fit i (by omega))
  · simp only [hashLay, List.length_cons, List.length_nil] at hi hj
    -- an empty buffer is apart from every other
    by_cases z : (hashLay L s K).size i = 0 ∨ (hashLay L s K).size j = 0
    · intro x hx hy
      rcases z with z | z
      · simp only [Region.Contains, z] at hx; omega
      · simp only [Region.Contains, z] at hy; omega
    have hKi : i ≤ 1 ∨ K i = true := by
      rcases (by omega : i ≤ 1 ∨ 2 ≤ i) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl <;>
          exact z (.inl (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hKj : j ≤ 1 ∨ K j = true := by
      rcases (by omega : j ≤ 1 ∨ 2 ≤ j) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl <;>
          exact z (.inr (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hw : i ∈ Wb ∨ j ∈ Wb := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h'
      · exact .inl h.w0
      · exact .inl h.w1
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h''
      · exact .inr h.w0
      · exact .inr h.w1
      exact hK i hi j hj hij h' h'' (hKi.resolve_left (by omega)) (hKj.resolve_left (by omega))
    by_cases ei : i = 1
    · subst ei
      rw [b1]
      exact (hL.disj 1 (by omega) j (by omega) hij hw).sub_left hsub |>.sub_right (bi j hj (Ne.symm hij))
    · by_cases ej : j = 1
      · subst ej
        rw [b1]
        exact ((hL.disj i (by omega) 1 (by omega) hij hw).sub_right hsub).sub_left (bi i hi ei)
      · exact ((hL.disj i (by omega) j (by omega) hij hw).sub_left (bi i hi ei)).sub_right (bi j hj ej)

theorem Site.ctx : Ctx (hashLay L s K) s :=
  ⟨hashLay_ok h hK, by rw [hashLay_size L s (by decide) (.inl rfl) (by decide)]; exact h.sz0, rfl, by simp [hashLay],
    by rw [h.r7]; rfl, Nat.le_trans h.s8 h.spk, by simp [hashLay],
    by rw [show (⟨State.addr ((hashLay L s K).ptr 0), (hashLay L s K).size 0⟩ : Region) = L.buf 0 from rfl]
       exact h.cw 0 h.w0 (by decide)⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
