import VerifiedGarbage.Proof.Rc4.AArch64.Output
import VerifiedGarbage.Proof.Rc4.Table

/-!
# The table registers as an RC4 context

The table registers hold the table `T` from the base `B` (`TableIn`): byte
`k` is `T[B + k]`. With `j - B` broadcast in `v0` and `-B` in `v14`
(`PrgaRegs`), one byte of the stream (`byte_ok`: a swap step and the
output) does what RC4's `step` does.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- `B` as a byte. -/
abbrev bB (B : Nat) : BitVec 8 := BitVec.ofNat 8 B

/-- The table registers hold `T` from the base `B`. -/
def TableIn (s : State) (B : Nat) (T : Table) : Prop :=
  ∀ k < 256, tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0

theorem ofNat_add_eq_iff {B k m : Nat} (hk : k < 256) (hm : m < 256) :
    BitVec.ofNat 8 (B + k) = BitVec.ofNat 8 (B + m) ↔ k = m := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

theorem ofNat_add_eq_j {B k : Nat} (hk : k < 256) (j : BitVec 8) :
    BitVec.ofNat 8 (B + k) = j ↔ k = (j - bB B).toNat := by
  have hj := j.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

/-- The swap of positions `l` and `J` of the registers' table is RC4's swap
of `B + l` and `j`. -/
theorem swapR_eq (T : Table) {B l : Nat} (hl : l < 256) {R : Nat → BitVec 8}
    (hR : ∀ k < 256, R k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0) (j : BitVec 8) {k : Nat}
    (hk : k < 256) :
    swapR R l (j - bB B).toNat k = (swap T (BitVec.ofNat 8 (B + l)) j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
  have hJ := (j - bB B).isLt
  have hJj : BitVec.ofNat 8 (B + (j - bB B).toNat) = j := (ofNat_add_eq_j hJ j).mpr rfl
  rw [swap_get]
  simp only [swapR, ofNat_add_eq_j hk j, ofNat_add_eq_iff hk hl]
  by_cases h1 : k = l
  · subst h1
    by_cases h2 : k = (j - bB B).toNat
    · simp only [ite_true, h2, hR _ hJ]
    · simp only [ite_true, h2, ite_false, hR _ hJ, hJj]
  · by_cases h2 : k = (j - bB B).toNat
    · have h1' : ¬ (j - bB B).toNat = l := fun h => h1 (h2.trans h)
      simp only [h2, h1', ite_true, ite_false, hR _ hl]
    · simp only [h1, h2, ite_false, hR _ hk]

/-- The PRGA's registers hold the context `c` from the base `B`: its table,
`j - B`, and `-B`. -/
structure PrgaRegs (s : State) (B : Nat) (c : Context) : Prop where
  table : TableIn s B c.table
  j : s.v (dq 0) = bc (c.j - bB B)
  nb : s.v negBase = bc (0 - bB B)
  consts : Consts s

theorem byte_add_sub (cj a B : BitVec 8) : cj - B + a = cj + a - B := by bv_omega

theorem idx_out (a b : BitVec 8) (B : Nat) :
    BitVec.ofNat 8 (B + (a + b + (0 - bB B)).toNat) = a + b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub,
    show (0 : BitVec 8).toNat = 0 from rfl]
  have := a.isLt; have := b.isLt
  omega

/-- One byte of the stream, at lane `l` of the group whose base is `B`. -/
theorem byte_ok {l : Nat} (hl : l < 16) {B : Nat} {c : Context} {s : State} (h : PrgaRegs s B c)
    (hi : c.i + 1 = BitVec.ofNat 8 (B + l)) (hsi : s.v si = bc (tbyte s.v l))
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block (swapStep true l ++ output)) s fun t =>
      PrgaRegs t B (step c).1 ∧ t.v si = bc (tbyte t.v (l + 1)) ∧
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ (step c).2) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ stepRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let T := c.table
  let i := c.i + 1
  let a := T.getD i.toNat 0
  let j := c.j + a
  let b := T.getD j.toNat 0
  have hR : ∀ k < 256, tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0 := h.table
  have ha : tbyte s.v l = a := by rw [hR l (by omega)]; simp only [a, i, hi]
  have hJ : c.j - bB B + tbyte s.v l = j - bB B := by rw [ha, byte_add_sub]
  obtain ⟨s₁, run₁, t₁, j₁, i₁, o6₁, o₁⟩ := swapStep_run true hl h.consts h.j hsi fun _ => h.nb
  rw [hJ] at t₁ j₁ i₁ o6₁
  have tab₁ : ∀ k < 256, tbyte s₁.v k = (swap T i j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
    intro k hk; rw [t₁ k hk, swapR_eq T (by omega) hR j hk, ← hi]
  have hb : tbyte s.v (j - bB B).toNat = b := by
    rw [hR _ (j - bB B).isLt, (ofNat_add_eq_j (j - bB B).isLt j).mpr rfl]
  have six₁ : s₁.v .v6 = bc (a + b + (0 - bB B)) := by rw [o6₁ rfl, ha, hb]
  have k₁ : Consts s₁ := consts_of_only h.consts o₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hd₁ : InRegions s₁.wr (s₁.gpr .x1) 1 := by rw [o₁.wr, o₁.gpr]; exact hd
  refine WP.mono (output_ok k₁ six₁ hd₁) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  have tt : tbyte t.v = tbyte s₁.v := by
    funext k; simp only [tbyte]; rw [v _ (by
      simp only [outRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v1 by decide).ne _, (show NotTable .v2 by decide).ne _,
        (show NotTable .v3 by decide).ne _, (show NotTable .v7 by decide).ne _⟩)]
  have step_c : step c = ({ table := swap T i j, i, j }, (swap T i j).getD (a + b).toNat 0) :=
    step_eq c
  rw [step_c]
  refine ⟨⟨fun k hk => by rw [tt, tab₁ k hk], by rw [v _ (by decide), j₁],
      by rw [v _ (by decide), o₁.2 _ (by decide), h.nb], k₁.congr fun r hr => v r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩,
    by rw [v _ (by decide), i₁, tt, t₁ _ (by omega)], ?_, by rw [x1, o₁.gpr], by rw [x2, o₁.gpr],
    fun r a b c d => by rw [g r a b c d, o₁.gpr], fun r hr => ?_, by rw [rd, o₁.rd],
    by rw [wr, o₁.wr], by rw [sp, o₁.sp]⟩
  · rw [m, o₁.mem, o₁.gpr, tab₁ _ (by exact (a + b + (0 - bB B)).isLt), idx_out]
  · have hr' : r ∉ outRegs := fun h' => hr (by
      simp only [outRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> decide)
    rw [v r hr', o₁.2 r hr]

end VG.Proof.Rc4.AArch64
