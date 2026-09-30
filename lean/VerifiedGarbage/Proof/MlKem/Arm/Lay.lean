import VerifiedGarbage.Proof.MlKem.Arm.Prims
import VerifiedGarbage.Impl.MlKem.Arm.Top

/-!
# ML-KEM-768 on 32-bit ARM: the buffers of the top-level functions

Untrusted: everything here is checked by Lean. The top-level functions
work on a few buffers (`Lay`): `scratch` (buffer 0), the 8 bytes below the
stack pointer (buffer 1), and their arguments; the contracts make them
pairwise disjoint (`Lay.Ok`). A region is `l` bytes at offset `o` of buffer
`i` (`Lay.R`), and two regions are disjoint when a computation on the
offsets says so (`sepB`, decided by the kernel), so what a call writes and
what the proofs keep track of are lists of triples `(i, o, l)`.

A state `s` in which the functions run their parts is `Ctx`: `r7` points to
`scratch`, and the stack pointer is the one of buffer 1. `Kept rs s s'`
(`Keccak.lean`) says what a part changes.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-- Buffers: their pointers and sizes. -/
structure Lay where
  ptr : Nat → BitVec 32
  sizes : List Nat

/-- Whether the regions `a` and `b` (buffer, offset, length) are within
their buffers and apart. -/
def sepB (sz : List Nat) (a b : Nat × Nat × Nat) : Bool :=
  a.1 < sz.length && b.1 < sz.length && a.2.1 + a.2.2 ≤ sz.getD a.1 0 && b.2.1 + b.2.2 ≤ sz.getD b.1 0 &&
    (a.1 != b.1 || a.2.1 + a.2.2 ≤ b.2.1 || b.2.1 + b.2.2 ≤ a.2.1)

/-- `a` is apart from every region of `W`. -/
def sepAll (sz : List Nat) (a : Nat × Nat × Nat) (W : List (Nat × Nat × Nat)) : Bool := W.all (sepB sz a)

namespace Lay

variable (L : Lay)

abbrev size (i : Nat) : Nat := L.sizes.getD i 0

/-- `l` bytes at offset `o` of buffer `i`. -/
abbrev R (i o l : Nat) : Region := ⟨State.addr (L.ptr i) + BitVec.ofNat 64 o, l⟩

/-- The regions of the triples `W`. -/
abbrev RL (W : List (Nat × Nat × Nat)) : List Region := W.map fun w => L.R w.1 w.2.1 w.2.2

/-- The buffers fit in the address space and are pairwise disjoint. -/
structure Ok : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

variable {L}

theorem R_sub {i o l : Nat} (h : o + l ≤ L.size i) :
    Region.Sub (L.R i o l) ⟨State.addr (L.ptr i), L.size i⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem disj (hL : L.Ok) {i o l j o' l' : Nat} (h : sepB L.sizes (i, o, l) (j, o', l') = true) :
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
  · exact ((hL.disj _ ha _ hb e).sub_left (R_sub hla)).sub_right (R_sub hlb)

theorem disjAll (hL : L.Ok) {i o l : Nat} {W : List (Nat × Nat × Nat)} (h : sepAll L.sizes (i, o, l) W = true) :
    ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := by
  intro r hr
  obtain ⟨⟨j, o', l'⟩, hw, rfl⟩ := List.mem_map.mp hr
  exact disj hL (List.all_eq_true.mp h _ hw)

/-- The address of a pointer into a buffer. -/
theorem addr_off (hL : L.Ok) {i o : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    State.addr (L.ptr i + BitVec.ofNat 32 o) = State.addr (L.ptr i) + BitVec.ofNat 64 o :=
  addr_add (by have := hL.fit i hi; omega)

theorem regA_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (ho : o < L.size i) :
    regA (L.ptr i + BitVec.ofNat 32 o) l = L.R i o l := by
  simp only [regA, addr_off hL hi ho]

theorem regA_zero (i l : Nat) : regA (L.ptr i) l = L.R i 0 l := by
  simp only [regA, Lay.R, add_ofNat_zero]

theorem fit_off (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i) (hl : 0 < l) :
    (L.ptr i + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 := by
  have := hL.fit i hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- A part of a buffer the state may access. -/
theorem covers {i o l : Nat} {ws : List Region} (hin : ⟨State.addr (L.ptr i), L.size i⟩ ∈ ws)
    (h : o + l ≤ L.size i) : Covers [L.R i o l] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, hin, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem polyIs_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 1024) W = true) {f : Poly}
    (hp : PolyIs m (State.addr (L.ptr i) + BitVec.ofNat 64 o) f) :
    PolyIs m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) f :=
  polyIs_frame hf (disjAll hL h) hp

theorem bytes_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hl : l ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' (State.addr (L.ptr i) + BitVec.ofNat 64 o) l =
      Spec.Sha3.bytesAt m (State.addr (L.ptr i) + BitVec.ofNat 64 o) l :=
  bytesAt_frame hf (disjAll hL h) hl

theorem word_keep (hL : L.Ok) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o : Nat} (h : sepAll L.sizes (i, o, 4) W = true) :
    m'.readW (State.addr (L.ptr i) + BitVec.ofNat 64 o) 32 = m.readW (State.addr (L.ptr i) + BitVec.ofNat 64 o) 32 :=
  hf.readW (Region.contains_self _ _) (disjAll hL h) (by decide)

/-- `Ok` from the disjointness of the buffers `i < j`. -/
theorem ok_of (hfit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32)
    (hd : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i < j →
      (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩) : L.Ok := by
  refine ⟨hfit, fun i hi j hj hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i hi j hj h
  · exact (hd j hj i hi h).symm

end Lay

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- The same, for regions given by triples. -/
theorem Kept.monoL {L : Lay} {W W' : List (Nat × Nat × Nat)} {s s' : State} (h : Kept (L.RL W) s s')
    (hs : ∀ w ∈ W, w ∈ W') : Kept (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

/-- A state that differs only in registers other than the callee-saved ones. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : Only s s') (rs : List Region) : Kept rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem Only.trans {s₁ s₂ s₃ : State} (h₁ : Only s₁ s₂) (h₂ : Only s₂ s₃) : Only s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.mem, h₁.mem], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], by rw [h₂.sp, h₁.sp]⟩

theorem Kept.only {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Only s₂ s₃) :
    Kept rs s₁ s₃ := h₁.trans (h₂.kept rs)

theorem Only.of_gpr {s : State} (g : Reg → BitVec 32) (h : ∀ r ∈ preserved, r ≠ .lr → g r = s.gpr r) :
    Only s { s with gpr := g } :=
  ⟨h, rfl, rfl, rfl, rfl⟩

/-! ## The setting of the parts -/

/-- `s` runs a part of a top-level function: `scratch` (buffer 0, writable,
of which the parts use the first 32768 bytes) in `r7`, and the 8 bytes
below the stack pointer (buffer 1). -/
structure Ctx (L : Lay) (s : State) : Prop where
  ok : L.Ok
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = 8
  len : 2 ≤ L.sizes.length
  r7 : s.gpr .r7 = L.ptr 0
  sp8 : 8 ≤ s.sp.toNat
  sp : L.ptr 1 = s.sp - BitVec.ofNat 32 8
  cw : (⟨State.addr (L.ptr 0), L.size 0⟩ : Region) ∈ s.wr

theorem Ctx.bel {L : Lay} {s : State} (h : Ctx L s) : below s 8 = L.R 1 0 8 := by
  simp only [Lay.R, h.sp, addr_sub h.sp8, add_ofNat_zero]

theorem Ctx.kept {L : Lay} {s s' : State} (h : Ctx L s) {rs : List Region} (hk : Kept rs s s') : Ctx L s' :=
  ⟨h.ok, h.sz0, h.sz1, h.len, by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.sp]; exact h.sp8,
    by rw [hk.sp]; exact h.sp, by rw [hk.wr]; exact h.cw⟩

theorem Ctx.only {L : Lay} {s s' : State} (h : Ctx L s) (hk : Only s s') : Ctx L s' := h.kept (hk.kept [])

/-- A part of `scratch` the state may write. -/
theorem Ctx.cs {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) :
    Covers [L.R 0 o l] s.wr := Lay.covers h.cw (Nat.le_trans hl h.sz0)

theorem Ctx.addr {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) :
    State.addr (L.ptr 0 + BitVec.ofNat 32 o) = State.addr (L.ptr 0) + BitVec.ofNat 64 o :=
  Lay.addr_off h.ok (by have := h.len; omega) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.regAo {L : Lay} {s : State} (h : Ctx L s) {o : Nat} (ho : o < 32768) (l : Nat) :
    regA (L.ptr 0 + BitVec.ofNat 32 o) l = L.R 0 o l :=
  Lay.regA_off h.ok (by have := h.len; omega) (Nat.lt_of_lt_of_le ho h.sz0)

theorem Ctx.fit {L : Lay} {s : State} (h : Ctx L s) : (L.ptr 0).toNat + 32768 ≤ 2 ^ 32 := by
  have := h.ok.fit 0 (by have := h.len; omega); have := h.sz0; omega

theorem Ctx.fitO {L : Lay} {s : State} (h : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768) (hl0 : 0 < l) :
    (L.ptr 0 + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 :=
  Lay.fit_off h.ok (by have := h.len; omega) (Nat.le_trans hl h.sz0) hl0

theorem Ctx.disj {L : Lay} {s : State} (h : Ctx L s) {a b : Nat × Nat × Nat} (hs : sepB L.sizes a b = true) :
    (L.R a.1 a.2.1 a.2.2).Disjoint (L.R b.1 b.2.1 b.2.2) := Lay.disj h.ok hs

end VG.Proof.MlKem.Arm
