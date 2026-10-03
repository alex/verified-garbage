import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs

/-!
# The constants, the operand sums and the shifted second operands

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-! ## Constants -/

theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block consts) s fun t =>
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧ t.v (V 31) = 0 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr = s.gpr ∧
      (∀ r : VReg, r ≠ V 30 → r ≠ V 31 → t.v r = s.v r) ∧ Scr t base := by
  refine WP.of_runBlock ⟨_, by
    simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, vo, VOp.eval,
      Option.map_some]; rfl, ?_⟩
  refine ⟨fun e he => ?_, ?_, rfl, rfl, rfl, by simp only [RegUpd.gpr_setV], fun r h1 h2 => ?_,
    scr_of hs (by simp only [RegUpd.gpr_setV]) rfl⟩
  · simp only [RegUpd.v_setV_of_ne _ _ (show V 30 ≠ V 31 by decide), RegUpd.v_setV_self]
    rw [vdword_ofVDwords _ _ he]
    split <;> rw [hs.mask] <;> rfl
  · simp only [RegUpd.v_setV_self]
  · simp only [RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

/-! ## Sums -/

/-- One step of `sums`: vector `i` of `a₀ + a₁` and of `b₀ + b₁`. -/
def sumChunk (i : Nat) : List Instr :=
  [ldq 0 (NA + 16 * i), ldq 1 (NA + 16 * (i + 4)), vo (.add .s4 (V 0) (V 0) (V 1)), stq 0 (NAS + 16 * i),
    ldq 2 (NB + 16 * i), ldq 3 (NB + 16 * (i + 4)), vo (.add .s4 (V 2) (V 2) (V 3)), stq 2 (NBS + 16 * i)]

theorem sums_eq : sums = (List.range 4).flatMap sumChunk := rfl

theorem vword_add (x y : BitVec 128) {c : Nat} (hc : c < 4) :
    (vword (VArr.s4.map2 (fun _ a b => a + b) x y) c).toNat = ((vword x c).toNat + (vword y c).toNat) % 2 ^ 32 := by
  rw [vword_map2 _ _ _ hc, BitVec.toNat_add]

theorem sumChunk_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 4) :
    WP isa (.block (sumChunk i)) s fun t =>
      (∀ c < 4, nw t.mem base (NAS + 16 * i + 4 * c) =
        (nw s.mem base (NA + 16 * i + 4 * c) + nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      (∀ c < 4, nw t.mem base (NBS + 16 * i + 4 * c) =
        (nw s.mem base (NB + 16 * i + 4 * c) + nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      Outside base NAS 128 s.mem t.mem ∧
      ((∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS + 16 * i ∨ NAS + 16 * i + 16 ≤ d) →
        (d + 4 ≤ NBS + 16 * i ∨ NBS + 16 * i + 16 ≤ d) → nw t.mem base d = nw s.mem base d)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  have n01 : V 0 ≠ V 1 := by decide
  have n10 : V 1 ≠ V 0 := by decide
  have n02 : V 0 ≠ V 2 := by decide
  have n20 : V 2 ≠ V 0 := by decide
  have n03 : V 0 ≠ V 3 := by decide
  have n30 : V 3 ≠ V 0 := by decide
  have n12 : V 1 ≠ V 2 := by decide
  have n21 : V 2 ≠ V 1 := by decide
  have n13 : V 1 ≠ V 3 := by decide
  have n31 : V 3 ≠ V 1 := by decide
  have n23 : V 2 ≠ V 3 := by decide
  have n32 : V 3 ≠ V 2 := by decide
  simp only [sumChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 0 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g1 1 (by omega) (by omega), ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g2 0 (by omega) (by omega), ?_⟩
  case g2 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g3 2 (by omega) (by omega), ?_⟩
  case g3 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g4 3 (by omega) (by omega), ?_⟩
  case g4 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g5 2 (by omega) (by omega), ?_⟩
  case g5 => scr
  refine WP.block_nil_iff.mpr ?_
  vred
  simp only [setMem_gpr, setMem_rd, setMem_wr, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV]
  generalize hm1 : s.mem.write (off base (NAS + 16 * i)) 16 _ = m1
  have o1 : Outside base (NAS + 16 * i) 16 s.mem m1 := hm1 ▸ st_outside _ _ _ (by omega)
  have r1 : ∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS + 16 * i ∨ NAS + 16 * i + 16 ≤ d) → nw m1 base d = nw s.mem base d :=
    fun d h1 h2 => Outside.nw o1 h2 h1
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_, fun d h1 h2 h3 => ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rw [nw_st_other _ _ _ (by omega) (by omega) (by omega), ← hm1, nw_st _ _ _ _ hc, vword_add _ _ hc,
      vword_ld _ _ _ hc, vword_ld _ _ _ hc]
  · rw [nw_st _ _ _ _ hc, vword_add _ _ hc, vword_ld _ _ _ hc, vword_ld _ _ _ hc, r1 _ (by omega) (by omega),
      r1 _ (by omega) (by omega)]
  · exact (o1.mono (by omega) (by omega)).trans ((st_outside _ base _ (by omega)).mono (by omega) (by omega))
  · rw [nw_st_other _ _ _ (by omega) h1 h3, r1 d h1 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r0, r1', r2, r3⟩ := hr
    simp only [setMem_v, RegUpd.v_setV_of_ne _ _ r0, RegUpd.v_setV_of_ne _ _ r1', RegUpd.v_setV_of_ne _ _ r2,
      RegUpd.v_setV_of_ne _ _ r3]

theorem sums_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block sums) s fun t =>
      (∀ i < 4, ∀ c < 4, nw t.mem base (NAS + 16 * i + 4 * c) =
        (nw s.mem base (NA + 16 * i + 4 * c) + nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      (∀ i < 4, ∀ c < 4, nw t.mem base (NBS + 16 * i + 4 * c) =
        (nw s.mem base (NB + 16 * i + 4 * c) + nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      Outside base NAS 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  rw [sums_eq]
  let inv := fun n (t : State) =>
    (∀ i < n, ∀ c < 4, nw t.mem base (NAS + 16 * i + 4 * c) =
      (nw s.mem base (NA + 16 * i + 4 * c) + nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
    (∀ i < n, ∀ c < 4, nw t.mem base (NBS + 16 * i + 4 * c) =
      (nw s.mem base (NB + 16 * i + 4 * c) + nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
    Outside base NAS 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨ta, tb, tO, tg, tr, tw, tv⟩ => ?_) 4
    (by decide) s ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), Outside.refl _ _ _ _,
      rfl, rfl, rfl, fun _ _ => rfl⟩) fun t ht => ht
  have ht : Scr t base := scr_of hs tg tw
  have same : ∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS ∨ NAS + 128 ≤ d) → nw t.mem base d = nw s.mem base d :=
    fun d h1 h2 => Outside.nw tO h2 h1
  refine WP.mono (sumChunk_ok ht hn) fun u ⟨ua, ub, uO, uk, ug, ur, uw, uv⟩ =>
    ⟨fun i hi c hc => ?_, fun i hi c hc => ?_, tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr,
      uw.trans tw, fun r hr => (uv r hr).trans (tv r hr)⟩
  · rcases (show i < n ∨ i = n by omega) with h | rfl
    · rw [uk _ (by omega) (by omega) (by omega)]; exact ta i h c hc
    · rw [ua c hc, same _ (by omega) (by omega), same _ (by omega) (by omega)]
  · rcases (show i < n ∨ i = n by omega) with h | rfl
    · rw [uk _ (by omega) (by omega) (by omega)]; exact tb i h c hc
    · rw [ub c hc, same _ (by omega) (by omega), same _ (by omega) (by omega)]

/-! ## Shifted second operands -/

/-- Word `c` of shifted vector `j` of half `h`, from the words `w` of memory. -/
def shw (w : Nat → Nat) (h j c : Nat) : Nat :=
  if c < 2 then (if j = 0 then 0 else w (bHalf h + 16 * (j - 1) + 4 * (c + 2)))
  else (if j = 4 then 0 else w (bHalf h + 16 * j + 4 * (c - 2)))

def shiftChunk (h : Nat) : List Instr :=
  [ldq 0 (bHalf h + 16 * 0), ldq 1 (bHalf h + 16 * 1), ldq 2 (bHalf h + 16 * 2), ldq 3 (bHalf h + 16 * 3),
    vo (.ext (V 4) (V 31) (V 0) 8), vo (.ext (V 5) (V 0) (V 1) 8), vo (.ext (V 6) (V 1) (V 2) 8),
    vo (.ext (V 7) (V 2) (V 3) 8), vo (.ext (V 8) (V 3) (V 31) 8),
    stq 4 (NBP + 80 * h + 16 * 0), stq 5 (NBP + 80 * h + 16 * 1), stq 6 (NBP + 80 * h + 16 * 2),
    stq 7 (NBP + 80 * h + 16 * 3), stq 8 (NBP + 80 * h + 16 * 4)]

theorem shifted_eq : shifted = (List.range 3).flatMap shiftChunk := rfl

theorem bHalf_lt (h : Nat) : NB ≤ bHalf h ∧ bHalf h + 64 ≤ NBS + 64 ∧ bHalf h % 16 = 0 := by
  unfold bHalf NB NBS NA; split <;> omega

theorem ext_words (n m : BitVec 128) (c : Nat) (hc : c < 4) :
    (vword (extv n m) c).toNat = if c < 2 then (vword n (c + 2)).toNat else (vword m (c - 2)).toNat := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [ext8_0]; rfl
  · rw [ext8_1]; rfl
  · rw [ext8_2]; rfl
  · rw [ext8_3]; rfl

theorem shw_0 (w : Nat → Nat) (h c : Nat) :
    shw w h 0 c = if c < 2 then 0 else w (bHalf h + 16 * 0 + 4 * (c - 2)) := by simp [shw]
theorem shw_1 (w : Nat → Nat) (h c : Nat) :
    shw w h 1 c = if c < 2 then w (bHalf h + 16 * 0 + 4 * (c + 2)) else w (bHalf h + 16 * 1 + 4 * (c - 2)) := by
  simp [shw]
theorem shw_2 (w : Nat → Nat) (h c : Nat) :
    shw w h 2 c = if c < 2 then w (bHalf h + 16 * 1 + 4 * (c + 2)) else w (bHalf h + 16 * 2 + 4 * (c - 2)) := by
  simp [shw]
theorem shw_3 (w : Nat → Nat) (h c : Nat) :
    shw w h 3 c = if c < 2 then w (bHalf h + 16 * 2 + 4 * (c + 2)) else w (bHalf h + 16 * 3 + 4 * (c - 2)) := by
  simp [shw]
theorem shw_4 (w : Nat → Nat) (h c : Nat) :
    shw w h 4 c = if c < 2 then w (bHalf h + 16 * 3 + 4 * (c + 2)) else 0 := by simp [shw]

theorem shiftChunk_ok {s : State} {base : Addr} (hs : Scr s base) {h : Nat} (hh : h < 3)
    (h31 : s.v (V 31) = 0) :
    WP isa (.block (shiftChunk h)) s fun t =>
      (∀ j < 5, ∀ c < 4, nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = shw (nw s.mem base) h j c) ∧
      Outside base (NBP + 80 * h) 80 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r) := by
  have hNBP : NBP = 4480 := rfl
  obtain ⟨b1, b2, b3⟩ := bHalf_lt h
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  have ne : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := V_ne
  have n0_31 := ne 0 (by decide) 31 (by decide) (by decide)
  have n31_0 := ne 31 (by decide) 0 (by decide) (by decide)
  simp only [shiftChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 0 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g1 1 (by omega) (by omega), ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g2 2 (by omega) (by omega), ?_⟩
  case g2 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g3 3 (by omega) (by omega), ?_⟩
  case g3 => scr
  simp only [RegUpd.mem_setV]
  generalize hL : s.mem.read (off base (bHalf h + 16 * 0)) 16 = L0
  generalize hL1 : s.mem.read (off base (bHalf h + 16 * 1)) 16 = L1
  generalize hL2 : s.mem.read (off base (bHalf h + 16 * 2)) 16 = L2
  generalize hL3 : s.mem.read (off base (bHalf h + 16 * 3)) 16 = L3
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  simp (config := {decide := true}) only [RegUpd.v_setV, ite_true, ite_false, h31]
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g4 4 (by omega) (by omega), ?_⟩
  case g4 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g5 5 (by omega) (by omega), ?_⟩
  case g5 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g6 6 (by omega) (by omega), ?_⟩
  case g6 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g7 7 (by omega) (by omega), ?_⟩
  case g7 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g8 8 (by omega) (by omega), ?_⟩
  case g8 => scr
  refine WP.block_nil_iff.mpr ?_
  simp (config := {decide := true}) only [RegUpd.v_setV, setMem_v, setMem_mem, RegUpd.mem_setV, ite_true,
    ite_false, setMem_gpr, setMem_rd, setMem_wr, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    show ∀ x y : BitVec 128, BitVec.extractLsb' 0 128 ((y ++ x) >>> (8 * 8)) = extv x y from fun _ _ => rfl]
  have w0 : ∀ c < 4, (vword (0 : BitVec 128) c).toNat = 0 := fun c _ => by simp [vword]
  have wL : ∀ k < 4, ∀ c < 4, (vword (s.mem.read (off base (bHalf h + 16 * k)) 16) c).toNat =
      nw s.mem base (bHalf h + 16 * k + 4 * c) := fun k _ c hc => vword_ld _ _ _ hc
  rw [← hL] at *
  rw [← hL1, ← hL2, ← hL3]
  generalize hm : s.mem.write (off base (NBP + 80 * h + 16 * 0)) 16 _ = m0
  have E : ∀ (x y : BitVec 128) (c : Nat), c < 4 → (vword (extv x y) c).toNat =
      if c < 2 then (vword x (c + 2)).toNat else (vword y (c - 2)).toNat := fun x y c hc => ext_words x y c hc
  refine ⟨fun j hj c hc => ?_, ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st_other _ _ _ (by omega) (by omega) (by omega),
        nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st_other _ _ _ (by omega) (by omega) (by omega),
        ← hm, nw_st _ _ _ _ hc, E _ _ c hc, shw_0]
      split
      · exact w0 _ (by omega)
      · exact wL 0 (by decide) _ (by omega)
    · rw [nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st_other _ _ _ (by omega) (by omega) (by omega),
        nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st _ _ _ _ hc, E _ _ c hc, shw_1]
      split
      · exact wL 0 (by decide) _ (by omega)
      · exact wL 1 (by decide) _ (by omega)
    · rw [nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st_other _ _ _ (by omega) (by omega) (by omega),
        nw_st _ _ _ _ hc, E _ _ c hc, shw_2]
      split
      · exact wL 1 (by decide) _ (by omega)
      · exact wL 2 (by decide) _ (by omega)
    · rw [nw_st_other _ _ _ (by omega) (by omega) (by omega), nw_st _ _ _ _ hc, E _ _ c hc, shw_3]
      split
      · exact wL 2 (by decide) _ (by omega)
      · exact wL 3 (by decide) _ (by omega)
    · rw [nw_st _ _ _ _ hc, E _ _ c hc, shw_4]
      split
      · exact wL 3 (by decide) _ (by omega)
      · exact w0 _ (by omega)
  · rw [← hm]
    exact ((st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      ((st_outside _ base _ (by omega)).mono (by omega) (by omega)))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
    simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, ite_false]

theorem shifted_ok {s : State} {base : Addr} (hs : Scr s base) (h31 : s.v (V 31) = 0) :
    WP isa (.block shifted) s fun t =>
      (∀ h < 3, ∀ j < 5, ∀ c < 4, nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = shw (nw s.mem base) h j c) ∧
      Outside base NBP 240 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r) := by
  have hNBP : NBP = 4480 := rfl
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  rw [shifted_eq]
  let inv := fun n (t : State) =>
    (∀ h < n, ∀ j < 5, ∀ c < 4, nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = shw (nw s.mem base) h j c) ∧
    Outside base NBP 240 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 3) inv (fun n t hn ⟨ta, tO, tg, tr, tw, tv⟩ => ?_) 3
    (by decide) s ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun t ht => ht
  have ht : Scr t base := scr_of hs tg tw
  have t31 : t.v (V 31) = 0 := by rw [tv _ (by decide)]; exact h31
  refine WP.mono (shiftChunk_ok ht hn t31) fun u ⟨ua, uO, ug, ur, uw, uv⟩ =>
    ⟨fun h hh j hj c hc => ?_, tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr,
      uw.trans tw, fun r hr => (uv r hr).trans (tv r hr)⟩
  rcases (show h < n ∨ h = n by omega) with hl | rfl
  · rw [Outside.nw uO (by omega) (by omega)]; exact ta h hl j hj c hc
  · rw [ua j hj c hc]
    obtain ⟨b1, b2, b3⟩ := bHalf_lt h
    have same : ∀ d, d + 4 ≤ NBP → nw t.mem base d = nw s.mem base d := fun d hd =>
      Outside.nw tO (Or.inl hd) (by omega)
    unfold shw
    split <;> split <;> first | rfl | exact same _ (by omega)

end VG.Proof.Curve448.AArch64.Neon
