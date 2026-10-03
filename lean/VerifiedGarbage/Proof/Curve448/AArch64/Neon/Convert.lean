import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range

/-!
# Splitting two elements' limbs into radix-2²⁸ vectors

Untrusted: everything here is checked by Lean. `convert x₁ x₂ dst` stores, as
word `c` of vector `i` at `dst`, the low 28 bits of limb `i` of element `c`
(`c < 2`) or the rest of limb `i` of element `c - 2`.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside word limbs)

/-- Word `c` of vector `i` of two elements' radix-2²⁸ limbs. -/
def split (f₁ f₂ : Nat → Nat) (i c : Nat) : Nat :=
  if c = 0 then f₁ i % 2 ^ 28 else if c = 1 then f₂ i % 2 ^ 28 else if c = 2 then f₁ i / 2 ^ 28 else f₂ i / 2 ^ 28

theorem V_ne : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := by decide

/-! ## Lanes of the conversion's operations -/

theorem lo28 (x m : BitVec 128) (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ 28 - 1) (e : Nat) (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ 28 := by
  rw [vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

theorem ushr28 (y x : BitVec 128) (e : Nat) (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr 28 w a b) y x) e).toNat = (vdword x e).toNat / 2 ^ 28 := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [map2_0]; simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [map2_1]; simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem vword_0 (x : BitVec 128) : (vword x 0).toNat = (vdword x 0).toNat % 2 ^ 32 := vword_lo x 0
theorem vword_2 (x : BitVec 128) : (vword x 2).toNat = (vdword x 1).toNat % 2 ^ 32 := vword_lo x 1

/-- The four words of `uzp1 r, lo, hi`, for `lo` and `hi` the low and high parts of `x`. -/
theorem uzp_words (lo hi : BitVec 128) (c : Nat) (hc : c < 4) :
    (vword (VPermOp.eval .uzp1 .s4 lo hi) c).toNat =
      if c = 0 then (vdword lo 0).toNat % 2 ^ 32 else if c = 1 then (vdword lo 1).toNat % 2 ^ 32
      else if c = 2 then (vdword hi 0).toNat % 2 ^ 32 else (vdword hi 1).toNat % 2 ^ 32 := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [uzp1_0, vword_0]; rfl
  · rw [uzp1_1, vword_2]; rfl
  · rw [uzp1_2, vword_0]; rfl
  · rw [uzp1_3, vword_2]; rfl


/-! ## Execution -/

theorem scr_setV {s : State} {base : Addr} (hs : Scr s base) (r : VReg) (x : BitVec 128) :
    Scr (s.setV r x) base := ⟨hs.x3, hs.mask, hs.wr, hs.nowrap⟩

theorem scr_mem {s : State} {base : Addr} (hs : Scr s base) (m : Mem) : Scr { s with mem := m } base :=
  ⟨hs.x3, hs.mask, hs.wr, hs.nowrap⟩

theorem exec_vo_of {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    isa.exec (vo op) s = some (s.setV d x) := by
  show (op.eval s).map (fun p => s.setV p.1 p.2) = _
  rw [h]; rfl

/-- One step of `convert`: limbs `2k` and `2k + 1` of both elements. -/
def convChunk (x₁ x₂ dst X Y P Q k : Nat) : List Instr :=
  [ldq X (x₁ + 16 * k), ldq Y (x₂ + 16 * k),
    vo (.perm .trn1 .d2 (V P) (V X) (V Y)), vo (.perm .trn2 .d2 (V Q) (V X) (V Y)),
    vo (.logic .and (V X) (V P) (V 30)), vo (.shift .ushr .d2 (V Y) (V P) 28),
    vo (.perm .uzp1 .s4 (V P) (V X) (V Y)), stq P (dst + 16 * (2 * k)),
    vo (.logic .and (V X) (V Q) (V 30)), vo (.shift .ushr .d2 (V Y) (V Q) 28),
    vo (.perm .uzp1 .s4 (V Q) (V X) (V Y)), stq Q (dst + 16 * (2 * k + 1))]

theorem convert_eq (x₁ x₂ dst X Y P Q : Nat) :
    convert x₁ x₂ dst X Y P Q = (List.range 4).flatMap (convChunk x₁ x₂ dst X Y P Q) := rfl

/-- A vector holding limbs `2k` of two elements (lanes 0 and 1), split. -/
theorem split_words {lo hi : BitVec 128} {a b : Nat}
    (hlo : ∀ e < 2, (vdword lo e).toNat = (if e = 0 then a else b) % 2 ^ 28)
    (hhi : ∀ e < 2, (vdword hi e).toNat = (if e = 0 then a else b) / 2 ^ 28)
    (ha : a < 2 ^ 60) (hb : b < 2 ^ 60) (c : Nat) (hc : c < 4) :
    (vword (VPermOp.eval .uzp1 .s4 lo hi) c).toNat =
      if c = 0 then a % 2 ^ 28 else if c = 1 then b % 2 ^ 28 else if c = 2 then a / 2 ^ 28 else b / 2 ^ 28 := by
  rw [uzp_words lo hi c hc, hlo 0 (by decide), hlo 1 (by decide), hhi 0 (by decide), hhi 1 (by decide)]
  simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
      show (3 : Nat) ≠ 2 by decide] <;> omega


theorem limb_ld (m : Mem) (base : Addr) (x k : Nat) (e : Nat) (he : e < 2) :
    (vdword (m.read (off base (x + 16 * k)) 16) e).toNat = limbs m base x (2 * k + e) := by
  rw [vdword_read16 _ _ he, off_add]
  simp only [limbs, word]
  congr 3
  omega

/-- What one step of `convert` does. -/
theorem convChunk_ok {s : State} {base : Addr} (hs : Scr s base) {x₁ x₂ dst X Y P Q k : Nat} (hk : k < 4)
    (h₁ : x₁ % 16 = 0) (h₁' : x₁ + 64 ≤ 8192) (h₂ : x₂ % 16 = 0) (h₂' : x₂ + 64 ≤ 8192)
    (hd : dst % 16 = 0) (hd' : dst + 128 ≤ 8192)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1)
    (nXY : V X ≠ V Y) (nXP : V X ≠ V P) (nXQ : V X ≠ V Q) (nYP : V Y ≠ V P) (nYQ : V Y ≠ V Q)
    (nPQ : V P ≠ V Q) (n30 : ∀ r ∈ [X, Y, P, Q], V r ≠ V 30)
    (hl₁ : ∀ i < 8, limbs s.mem base x₁ i < 2 ^ 60) (hl₂ : ∀ i < 8, limbs s.mem base x₂ i < 2 ^ 60) :
    WP isa (.block (convChunk x₁ x₂ dst X Y P Q k)) s fun t =>
      (∀ c < 4, nw t.mem base (dst + 16 * (2 * k) + 4 * c) =
        split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k) c) ∧
      (∀ c < 4, nw t.mem base (dst + 16 * (2 * k + 1) + 4 * c) =
        split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k + 1) c) ∧
      Outside base (dst + 32 * k) 32 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r) := by
  have e1 : x₁ + 16 * k + 16 ≤ 8192 := by omega
  have e2 : x₂ + 16 * k + 16 ≤ 8192 := by omega
  have a1 : (x₁ + 16 * k) % 16 = 0 := by omega
  have a2 : (x₂ + 16 * k) % 16 = 0 := by omega
  have dP : (dst + 16 * (2 * k)) % 16 = 0 := by omega
  have dQ : (dst + 16 * (2 * k + 1)) % 16 = 0 := by omega
  have dP' : dst + 16 * (2 * k) + 16 ≤ 8192 := by omega
  have dQ' : dst + 16 * (2 * k + 1) + 16 ≤ 8192 := by omega
  simp only [convChunk]
  -- the loads
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs X a1 e1, ?_⟩
  have hs1 := scr_setV hs (V X) (s.mem.read (off base (x₁ + 16 * k)) 16)
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs1 Y a2 e2, ?_⟩
  generalize hA : s.mem.read (off base (x₁ + 16 * k)) 16 = A at *
  simp only [RegUpd.mem_setV] at *
  generalize hB : s.mem.read (off base (x₂ + 16 * k)) 16 = B
  have hs2 := scr_setV hs1 (V Y) B
  have m30X : V 30 ≠ V X := (n30 X (by simp)).symm
  have m30Y : V 30 ≠ V Y := (n30 Y (by simp)).symm
  have m30P : V 30 ≠ V P := (n30 P (by simp)).symm
  have m30Q : V 30 ≠ V Q := (n30 Q (by simp)).symm
  have nYX := nXY.symm
  have nPX := nXP.symm
  have nQX := nXQ.symm
  have nPY := nYP.symm
  have nQY := nYQ.symm
  have nQP := nPQ.symm
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?h1 P dP dP', ?_⟩
  case h1 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?h2 Q dQ dQ', ?_⟩
  case h2 => scr
  vred
  refine WP.block_nil_iff.mpr ?_
  simp only [setMem_mem, setMem_gpr, setMem_rd, setMem_wr, setMem_v, RegUpd.gpr_setV, RegUpd.rd_setV,
    RegUpd.wr_setV]
  generalize hT1 : VPermOp.eval .trn1 .d2 A B = T1
  generalize hT2 : VPermOp.eval .trn2 .d2 A B = T2
  generalize hH1 : VArr.d2.map2 (fun w x y => VShiftOp.ushr.eval 28 w x y) B T1 = H1
  generalize hvP : VPermOp.eval .uzp1 .s4 (T1 &&& s.v (V 30)) H1 = vP
  generalize hvQ : VPermOp.eval .uzp1 .s4 (T2 &&& s.v (V 30))
    (VArr.d2.map2 (fun w x y => VShiftOp.ushr.eval 28 w x y) H1 T2) = vQ
  have lA : ∀ e < 2, (vdword A e).toNat = limbs s.mem base x₁ (2 * k + e) := fun e he => by
    rw [← hA]; exact limb_ld _ _ _ _ _ he
  have lB : ∀ e < 2, (vdword B e).toNat = limbs s.mem base x₂ (2 * k + e) := fun e he => by
    rw [← hB]; exact limb_ld _ _ _ _ _ he
  have wP : ∀ c < 4, (vword vP c).toNat = split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k) c := by
    intro c hc
    rw [← hvP, split_words (a := limbs s.mem base x₁ (2 * k)) (b := limbs s.mem base x₂ (2 * k))
      (fun e he => by
        rw [lo28 _ _ hM e he, ← hT1]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn1_0, lA 0 (by decide)]; rfl
        · rw [trn1_1, lB 0 (by decide)]; rfl)
      (fun e he => by
        rw [← hH1, ushr28 _ _ e he, ← hT1]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn1_0, lA 0 (by decide)]; rfl
        · rw [trn1_1, lB 0 (by decide)]; rfl)
      (hl₁ _ (by omega)) (hl₂ _ (by omega)) c hc]
    rfl
  have wQ : ∀ c < 4, (vword vQ c).toNat = split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k + 1) c := by
    intro c hc
    rw [← hvQ, split_words (a := limbs s.mem base x₁ (2 * k + 1)) (b := limbs s.mem base x₂ (2 * k + 1))
      (fun e he => by
        rw [lo28 _ _ hM e he, ← hT2]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn2_0, lA 1 (by decide)]; rfl
        · rw [trn2_1, lB 1 (by decide)]; rfl)
      (fun e he => by
        rw [ushr28 _ _ e he, ← hT2]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn2_0, lA 1 (by decide)]; rfl
        · rw [trn2_1, lB 1 (by decide)]; rfl)
      (hl₁ _ (by omega)) (hl₂ _ (by omega)) c hc]
    rfl
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rw [nw_st_other _ _ _ dQ' (by omega) (by omega), nw_st _ _ _ _ hc, wP c hc]
  · rw [nw_st _ _ _ _ hc, wQ c hc]
  · exact ((st_outside _ base _ dP').mono (by omega) (by omega)).trans
      ((st_outside _ base _ dQ').mono (by omega) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [RegUpd.v_setV_of_ne _ _ r1, RegUpd.v_setV_of_ne _ _ r2, RegUpd.v_setV_of_ne _ _ r3,
      RegUpd.v_setV_of_ne _ _ r4, setMem_v]


theorem split_congr {f₁ f₂ g₁ g₂ : Nat → Nat} {i : Nat} (h₁ : f₁ i = g₁ i) (h₂ : f₂ i = g₂ i) (c : Nat) :
    split f₁ f₂ i c = split g₁ g₂ i c := by
  simp only [split, h₁, h₂]

theorem limbs_outside {base : Addr} {m m' : Mem} {o n x : Nat} (h : Outside base o n m m')
    (hx : x + 64 ≤ o ∨ o + n ≤ x) (hx' : x + 64 ≤ 8192) {i : Nat} (hi : i < 8) :
    limbs m' base x i = limbs m base x i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

/-- `convert x₁ x₂ dst`: the radix-2²⁸ vectors of `[x₁]` and `[x₂]` at `dst`. -/
theorem convert_ok {s : State} {base : Addr} (hs : Scr s base) {x₁ x₂ dst X Y P Q : Nat}
    (h₁ : x₁ % 16 = 0) (h₁' : x₁ + 64 ≤ 8192) (h₂ : x₂ % 16 = 0) (h₂' : x₂ + 64 ≤ 8192)
    (hd : dst % 16 = 0) (hd' : dst + 128 ≤ 8192) (s₁ : x₁ + 64 ≤ dst ∨ dst + 128 ≤ x₁)
    (s₂ : x₂ + 64 ≤ dst ∨ dst + 128 ≤ x₂)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1)
    (nXY : V X ≠ V Y) (nXP : V X ≠ V P) (nXQ : V X ≠ V Q) (nYP : V Y ≠ V P) (nYQ : V Y ≠ V Q)
    (nPQ : V P ≠ V Q) (n30 : ∀ r ∈ [X, Y, P, Q], V r ≠ V 30)
    (hl₁ : ∀ i < 8, limbs s.mem base x₁ i < 2 ^ 60) (hl₂ : ∀ i < 8, limbs s.mem base x₂ i < 2 ^ 60) :
    WP isa (.block (convert x₁ x₂ dst X Y P Q)) s fun t =>
      (∀ i < 8, ∀ c < 4, nw t.mem base (dst + 16 * i + 4 * c) =
        split (limbs s.mem base x₁) (limbs s.mem base x₂) i c) ∧
      Outside base dst 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r) := by
  rw [convert_eq]
  let inv := fun n (t : State) =>
    (∀ i < 2 * n, ∀ c < 4, nw t.mem base (dst + 16 * i + 4 * c) =
      split (limbs s.mem base x₁) (limbs s.mem base x₂) i c) ∧
    Outside base dst 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tw, tO, tg, tr, twr, tv⟩ => ?_) 4
    (by decide) s ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun t ht => ⟨fun i hi => ht.1 i (by omega), ht.2⟩
  have ht : Scr t base := scr_of hs tg twr
  have t30 : t.v (V 30) = s.v (V 30) := tv _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(n30 X (by simp)).symm, (n30 Y (by simp)).symm, (n30 P (by simp)).symm, (n30 Q (by simp)).symm⟩)
  have l₁ : ∀ i < 8, limbs t.mem base x₁ i = limbs s.mem base x₁ i := fun i hi => limbs_outside tO s₁ h₁' hi
  have l₂ : ∀ i < 8, limbs t.mem base x₂ i = limbs s.mem base x₂ i := fun i hi => limbs_outside tO s₂ h₂' hi
  refine WP.mono (convChunk_ok ht hn h₁ h₁' h₂ h₂' hd hd' (by rw [t30]; exact hM) nXY nXP nXQ nYP nYQ nPQ n30
    (fun i hi => by rw [l₁ i hi]; exact hl₁ i hi) (fun i hi => by rw [l₂ i hi]; exact hl₂ i hi))
    fun u ⟨uP, uQ, uo, ug, ur, uw, uv⟩ => ⟨fun i hi c hc => ?_, tO.trans (uo.mono (by omega) (by omega)),
      ug.trans tg, ur.trans tr, uw.trans twr, fun r hr => (uv r hr).trans (tv r hr)⟩
  rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
  · rw [VG.Proof.Curve448.AArch64.Neon.Outside.nw uo (by omega) (by omega)]
    exact tw i h c hc
  · rw [uP c hc]; exact split_congr (l₁ _ (by omega)) (l₂ _ (by omega)) c
  · rw [uQ c hc]; exact split_congr (l₁ _ (by omega)) (l₂ _ (by omega)) c

end VG.Proof.Curve448.AArch64.Neon
