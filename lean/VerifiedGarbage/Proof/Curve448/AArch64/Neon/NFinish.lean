import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Carries
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Prep

/-!
# The radix-2⁵⁶ results

Untrusted: everything here is checked by Lean. The sixteen radix-2²⁸ limbs
become eight radix-2⁵⁶ limbs, limbs 0 and 4 carry into 1 and 5, and the
two elements' limbs are stored.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside word limbs)

theorem read16_write (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have := Mem.readW_writeW_self m p 16 v (by decide)
  simpa [Mem.readW, Mem.writeW] using this

theorem word_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {e : Nat} (he : e < 2) :
    word (m.write (off base d) 16 v) base (d + 8 * e) = vdword v e := by
  simp only [word]
  rw [← off_add, ← vdword_read16 _ _ he, read16_write]

def combineChunk (i : Nat) : List Instr :=
  [vo (.shift .shl .d2 (V (16 + i)) (V (2 * i + 1)) 28), vo (.add .d2 (V (16 + i)) (V (16 + i)) (V (2 * i)))]

def m56 : List Instr :=
  [vo (.shift .shl .d2 (V 31) (V 30) 28), vo (.add .d2 (V 31) (V 31) (V 30))]

def carry56 (i : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V i) 56), vo (.logic .and (V i) (V i) (V 31)),
    vo (.add .d2 (V (i + 1)) (V (i + 1)) (V 28))]

def outChunk (o₁ o₂ k : Nat) : List Instr :=
  [vo (.perm .trn1 .d2 (V 8) (V (16 + 2 * k)) (V (17 + 2 * k))),
    vo (.perm .trn2 .d2 (V 9) (V (16 + 2 * k)) (V (17 + 2 * k))), stq 8 (o₁ + 16 * k), stq 9 (o₂ + 16 * k)]

theorem finish_eq (o₁ o₂ : Nat) :
    finish o₁ o₂ = (List.range 8).flatMap combineChunk ++ m56 ++ ([16, 20].flatMap carry56) ++
      (List.range 4).flatMap (outChunk o₁ o₂) := rfl

theorem combineChunk_ok {s : State} {i : Nat} (hi : i < 8) {lo hi' : Nat → Nat}
    (hl : LaneIs s (2 * i) lo) (hh : LaneIs s (2 * i + 1) hi') (hlo : ∀ e < 2, lo e < 2 ^ 63)
    (hhi : ∀ e < 2, hi' e < 2 ^ 28) :
    WP isa (.block (combineChunk i)) s fun t =>
      LaneIs t (16 + i) (fun e => lo e + 2 ^ 28 * hi' e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, r ≠ V (16 + i) → t.v r = s.v r) := by
  have n1 : V (2 * i + 1) ≠ V (16 + i) := V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V (2 * i) ≠ V (16 + i) := V_ne _ (by omega) _ (by omega) (by omega)
  simp only [combineChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_self, lane_shl _ _ _ he,
      RegUpd.v_setV_of_ne _ _ n2, hl e he, hh e he]
    have := hlo e he; have := hhi e he
    rw [Nat.mod_eq_of_lt (by omega : hi' e * 2 ^ 28 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    dsimp only
    omega
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem combine_ok {s : State} (L : Nat → Nat → Nat) (hL : ∀ k < 16, LaneIs s k (L k))
    (he : ∀ i < 8, ∀ e < 2, L (2 * i) e < 2 ^ 63) (ho : ∀ i < 8, ∀ e < 2, L (2 * i + 1) e < 2 ^ 28) :
    WP isa (.block ((List.range 8).flatMap combineChunk)) s fun t =>
      (∀ i < 8, LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < 8, r ≠ V (16 + i)) → t.v r = s.v r) := by
  let inv := fun n (t : State) =>
    (∀ i < n, LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < n, r ≠ V (16 + i)) → t.v r = s.v r)
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ti, tm, tg, tr, tw, tv⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (by omega), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have keep : ∀ k < 16, t.v (V k) = s.v (V k) := fun k hk =>
    tv _ fun i hi => V_ne _ (by omega) _ (by omega) (by omega)
  refine WP.mono (combineChunk_ok hn (fun e he' => by rw [keep _ (by omega)]; exact hL _ (by omega) e he')
    (fun e he' => by rw [keep _ (by omega)]; exact hL _ (by omega) e he') (he n hn) (ho n hn))
    fun u ⟨ua, um, ug, ur, uw, uv⟩ => ⟨fun i hi => ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
      fun r hr => (uv r (hr n (by omega))).trans (tv r fun i hi => hr i (by omega))⟩
  rcases (show i < n ∨ i = n by omega) with h | rfl
  · intro e he'
    rw [uv _ (V_ne (16 + i) (by omega) (16 + n) (by omega) (by omega))]
    exact ti i h e he'
  · exact ua

theorem m56_ok {s : State} (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block m56) s fun t =>
      (∀ e < 2, (vdword (t.v (V 31)) e).toNat = 2 ^ 56 - 1) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr ∧ (∀ r : VReg, r ≠ V 31 → t.v r = s.v r) := by
  have n : V 30 ≠ V 31 := V_ne _ (by omega) _ (by omega) (by omega)
  simp only [m56]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV],
    by simp only [RegUpd.gpr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n, RegUpd.v_setV_self,
      lane_shl _ _ _ he, hM e he]
    decide
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem carry56_ok {s : State} {i : Nat} (hi : i = 16 ∨ i = 20)
    (hM : ∀ e < 2, (vdword (s.v (V 31)) e).toNat = 2 ^ 56 - 1) {x y : Nat → Nat}
    (hx : LaneIs s i x) (hy : LaneIs s (i + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 56 < 2 ^ 64) :
    WP isa (.block (carry56 i)) s fun t =>
      LaneIs t i (fun e => x e % 2 ^ 56) ∧ LaneIs t (i + 1) (fun e => y e + x e / 2 ^ 56) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ≠ V 28 → r ≠ V i → r ≠ V (i + 1) → t.v r = s.v r) := by
  have n1 : V 28 ≠ V i := V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V 28 ≠ V (i + 1) := V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V i ≠ V (i + 1) := V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 31 ≠ V 28 := V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 31 ≠ V i := V_ne _ (by omega) _ (by omega) (by omega)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [carry56]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r h1 h2 h3 => ?_⟩⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n3',
      RegUpd.v_setV_of_ne _ _ n2', RegUpd.v_setV_of_ne _ _ n1, RegUpd.v_setV_self, lane_ushr _ _ _ he, hx e he,
      hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

theorem outChunk_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ k : Nat} (hk : k < 4)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) :
    WP isa (.block (outChunk o₁ o₂ k)) s fun t =>
      (∀ j < 2, word t.mem base (o₁ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 0) ∧
      (∀ j < 2, word t.mem base (o₂ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 1) ∧
      VG.Proof.X448.AArch64.Outside2 base (o₁ + 16 * k) 16 (o₂ + 16 * k) 16 s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 8 → r ≠ V 9 → t.v r = s.v r) := by
  have n89 : V 8 ≠ V 9 := V_ne _ (by omega) _ (by omega) (by omega)
  have n98 := n89.symm
  have a8 : V (16 + 2 * k) ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have b8 : V (17 + 2 * k) ≠ V 8 := V_ne _ (by omega) _ (by omega) (by omega)
  have a9 : V (16 + 2 * k) ≠ V 9 := V_ne _ (by omega) _ (by omega) (by omega)
  have b9 : V (17 + 2 * k) ≠ V 9 := V_ne _ (by omega) _ (by omega) (by omega)
  simp only [outChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g1 8 (by omega) (by omega), ?_⟩
  case g1 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g2 9 (by omega) (by omega), ?_⟩
  case g2 => scr
  refine WP.block_nil_iff.mpr ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, fun r h8 h9 => ?_⟩
  · simp only [setMem_mem]
    rw [VG.Proof.X448.AArch64.Outside.word (st_outside _ base _ (by omega)) (by omega) (by omega),
      show o₁ + 8 * (2 * k + j) = o₁ + 16 * k + 8 * j by omega, word_st _ _ _ _ hj]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [trn1_0]; rfl
    · rw [trn1_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega]
  · simp only [setMem_mem, setMem_v]
    rw [show o₂ + 8 * (2 * k + j) = o₂ + 16 * k + 8 * j by omega, word_st _ _ _ _ hj, RegUpd.v_setV_self]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [trn2_0]; rfl
    · rw [trn2_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega]
  · simp only [setMem_mem]
    intro p hp hq
    rw [st_outside _ base _ (by omega) p hq, st_outside _ base _ (by omega) p hp]
  · simp only [setMem_gpr, RegUpd.gpr_setV]
  · simp only [setMem_rd, RegUpd.rd_setV]
  · simp only [setMem_wr, RegUpd.wr_setV]
  · simp only [setMem_v, RegUpd.v_setV_of_ne _ _ h9, RegUpd.v_setV_of_ne _ _ h8]

/-- The radix-2⁵⁶ limbs of the sixteen limbs `L`, before the last carries. -/
abbrev w56 (L : Nat → Nat) (i : Nat) : Nat := L (2 * i) + 2 ^ 28 * L (2 * i + 1)

/-- The results: limbs 0 and 4 carried into 1 and 5. -/
def out56 (L : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then w56 L 0 % 2 ^ 56 else if i = 1 then w56 L 1 + w56 L 0 / 2 ^ 56
  else if i = 4 then w56 L 4 % 2 ^ 56 else if i = 5 then w56 L 5 + w56 L 4 / 2 ^ 56 else w56 L i

theorem finishN_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ : Nat} (L : Nat → Nat → Nat)
    (hL : ∀ k < 16, LaneIs s k (fun e => L e k))
    (he : ∀ e < 2, ∀ i < 8, L e (2 * i) < 2 ^ 40) (ho : ∀ e < 2, ∀ i < 8, L e (2 * i + 1) < 2 ^ 28)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block (finish o₁ o₂)) s fun t =>
      (∀ i < 8, limbs t.mem base o₁ i = out56 (L 0) i) ∧ (∀ i < 8, limbs t.mem base o₂ i = out56 (L 1) i) ∧
      VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr := by
  rw [finish_eq, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (combine_ok (fun k e => L e k) hL (fun i hi e he' => by have := he e he' i hi; omega)
    (fun i hi e he' => ho e he' i hi)) fun t ⟨tw, tm, tg, tr, twr, tv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (m56_ok (fun e he' => by
    rw [tv _ (fun i _ => V_ne _ (by omega) _ (by omega) (by omega))]; exact hM e he')) fun u ⟨uM, um, ur, uw, ug, uv⟩ => ?_
  have hu : ∀ i < 8, LaneIs u (16 + i) (fun e => w56 (L e) i) := fun i hi e he' => by
    rw [uv _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact tw i hi e he'
  rw [WP.block_append_iff]
  -- the last carries
  have b0 : ∀ e < 2, ∀ i < 8, w56 (L e) i < 2 ^ 57 := fun e he' i hi => by
    have := he e he' i hi; have := ho e he' i hi; simp only [w56]; omega
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (carry56_ok (i := 16) (Or.inl rfl) uM (hu 0 (by decide)) (hu 1 (by decide))
    (fun e he' => by have := b0 e he' 1 (by decide); have := b0 e he' 0 (by decide); omega))
    fun v ⟨va, vb, vm, vg, vr, vw, vv⟩ => ?_
  have vM : ∀ e < 2, (vdword (v.v (V 31)) e).toNat = 2 ^ 56 - 1 := fun e he' => by
    rw [vv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
      (V_ne _ (by omega) _ (by omega) (by omega))]; exact uM e he'
  have v4 : LaneIs v 20 (fun e => w56 (L e) 4) := fun e he' => by
    rw [vv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
      (V_ne _ (by omega) _ (by omega) (by omega))]; exact hu 4 (by decide) e he'
  have v5 : LaneIs v 21 (fun e => w56 (L e) 5) := fun e he' => by
    rw [vv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
      (V_ne _ (by omega) _ (by omega) (by omega))]; exact hu 5 (by decide) e he'
  refine WP.mono (carry56_ok (i := 20) (Or.inr rfl) vM v4 v5
    (fun e he' => by have := b0 e he' 5 (by decide); have := b0 e he' 4 (by decide); omega))
    fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
  -- the results
  have wl : ∀ i < 8, LaneIs w (16 + i) (fun e => out56 (L e) i) := by
    intro i hi e he'
    rcases (show i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 4 ∧ i ≠ 5) by omega)
      with rfl | rfl | rfl | rfl | ⟨i0, i1, i4, i5⟩
    · rw [wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)), va e he']; simp [out56]
    · rw [wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)), vb e he']; simp [out56]
    · rw [wa e he']; simp [out56]
    · rw [wb e he']; simp [out56]
    · rw [wv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)),
        vv _ (V_ne _ (by omega) _ (by omega) (by omega)) (V_ne _ (by omega) _ (by omega) (by omega))
        (V_ne _ (by omega) _ (by omega) (by omega)), hu i hi e he']
      simp [out56, i0, i1, i4, i5]
  have gw : w.gpr = s.gpr := by rw [wg, vg, ug, tg]
  have hw : Scr w base := scr_of hs gw (by rw [ww, vw, uw, twr])
  let inv := fun n (x : State) =>
    (∀ i < 2 * n, (word x.mem base (o₁ + 8 * i)).toNat = out56 (L 0) i) ∧
    (∀ i < 2 * n, (word x.mem base (o₂ + 8 * i)).toNat = out56 (L 1) i) ∧
    VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 w.mem x.mem ∧ x.gpr = w.gpr ∧ x.rd = w.rd ∧ x.wr = w.wr ∧
    (∀ i < 8, x.v (V (16 + i)) = w.v (V (16 + i)))
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n x hn ⟨x1, x2, xo, xg, xr, xw, xv⟩ => ?_) 4
    (by decide) w ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      VG.Proof.X448.AArch64.Outside2.refl _ _ _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun x ⟨x1, x2, xo, xg, xr, xw, _⟩ => ⟨fun i hi => x1 i (by omega), fun i hi => x2 i (by omega), ?_,
      by rw [xr, wr, vr, ur, tr], by rw [xw, ww, vw, uw, twr], by rw [xg, gw]⟩
  · have hx : Scr x base := ⟨by rw [xg]; exact hw.x3, by rw [xg]; exact hw.mask, xw ▸ hw.wr, hw.nowrap⟩
    refine WP.mono (outChunk_ok hx hn h₁ h₁' h₂ h₂' h12) fun y ⟨y1, y2, yo, yg, yr, yw, yv⟩ =>
      ⟨fun i hi => ?_, fun i hi => ?_, xo.trans fun p hp hq => yo p (by omega) (by omega), yg.trans xg,
        yr.trans xr, yw.trans xw, fun i hi => (yv _ (V_ne _ (by omega) _ (by omega) (by omega))
          (V_ne _ (by omega) _ (by omega) (by omega))).trans (xv i hi)⟩
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega) (by omega) (by omega)]
        exact x1 i h
      · rw [show o₁ + 8 * (2 * n) = o₁ + 8 * (2 * n + 0) by omega, y1 0 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 0 (by decide)
      · rw [y1 1 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 0 (by decide)
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega) (by omega) (by omega)]
        exact x2 i h
      · rw [show o₂ + 8 * (2 * n) = o₂ + 8 * (2 * n + 0) by omega, y2 0 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 1 (by decide)
      · rw [y2 1 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 1 (by decide)
  · intro p hp hq
    rw [xo p hp hq, wm, vm, um, tm]

end VG.Proof.Curve448.AArch64.Neon
