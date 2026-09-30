import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge

/-!
# ML-DSA on 32-bit ARM: the sampling functions' prologue and epilogue

Untrusted: everything here is checked by Lean. The prologue (`pro`) saves
our caller's `r4`–`r11` and `lr` in the working space and sets up the
layout: from what it leaves, `J0` holds (`pro_ok`, for any registers, and
`pro_rn`, `pro_rb`, `pro_ball` for the three ways the functions call it).
The epilogue (`epi`) restores them: with `Env`, the calling convention's
obligations hold at the end (`epi_ok`, `retEpi_ok`, which also returns
`j >> 8`). The pieces of the loops: `storeJ` stores the next coefficient
`a[j]` (`storeJ_ok`), `jFull` tests `j ≥ 256` (`jFull_ok`), `step` advances
(`step_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne sp_setReg mem_setReg)
open VG.Proof.MlKem.Arm.Sample (Regs regs_cs)
open VG.Impl.MlDsa.Arm.Sample
open VG.Impl.MlKem.Arm (saveRegs restoreRegs savedRegs)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.Sample (coeffAddr coeff_contains Stored stored_snoc zw)

/-! ## The prologue -/

theorem savedRegs_preserved : ∀ i < 8, savedRegs.getD i .r4 ∈ preserved := by decide

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- A part of the working space, in the writable regions of the entry state. -/
theorem inScrσ {a n : Nat} (h : a + n ≤ 2048) : InRegions σ.wr (P.at' a) n := by
  rw [hp.wr]
  exact ⟨P.scrR, by simp, Offset.contains_base _ h (by omega)⟩

/-- The prologue, from a state `s` that differs from the entry state `σ`
only in registers that are not callee-saved, given what its moves leave. -/
theorem pro_ok {scr a msg : Reg} {prm len : Op2} {s : State} (hm : s.mem = σ.mem) (hrd : s.rd = σ.rd)
    (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp) (hcs : ∀ r ∈ preserved, s.gpr r = σ.gpr r)
    (hscr : s.gpr scr = P.scr)
    (hmv : ∀ t : State, t.gpr = s.gpr → WP isa (.block [.mov .r5 (.reg a), .mov .r6 (.reg scr), .mov .r7 prm,
      .mov .r8 (.reg msg), .mov .r9 len]) t fun t' => t'.gpr .r5 = P.a ∧ t'.gpr .r6 = P.scr ∧
        t'.gpr .r7 = P.prm ∧ t'.gpr .r8 = P.sd ∧ t'.gpr .r9 = BitVec.ofNat 32 P.len ∧ t'.mem = t.mem ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp) :
    WP isa (.block (pro scr a prm len msg)) s (J0 P σ) := by
  have fs := hp.fscr
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok scr (off := 2012) (by decide) (by rw [hscr]; omega) fun i hi => by
    rw [hscr, add_ofNat_add, hwr]; exact inScrσ hp (by omega)) fun s1 h1 => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ea : State.addr (s1.gpr scr + BitVec.ofNat 32 (2012 + 32)) = P.at' 2044 := by
    rw [h1.gpr, hscr]; exact at_eq hp (by decide)
  refine WP.mono (Q := fun s2 => s2 = { s1 with mem := s1.mem.writeW (P.at' 2044) (s1.gpr .lr) }) ?_
    fun s2 e2 => ?_
  · apply WP.of_runBlock
    rw [runBlock_cons, exec_str (by decide) (by rw [ea, h1.wr, hwr]; exact inScrσ hp (by omega)), runStep_some,
      runBlock_nil]
    exact ⟨_, rfl, by rw [ea]⟩
  subst e2
  refine WP.mono (hmv _ h1.gpr) fun s3 ⟨g5, g6, g7, g8, g9, m3, rd3, wr3, sp3⟩ => ⟨⟨?_, ?_, ?_, g5, g6, ?_, ?_, ?_⟩,
    g7, g8, g9⟩
  · rw [rd3, h1.rd, hrd]
  · rw [wr3, h1.wr, hwr]
  · rw [sp3, h1.sp, hsp]
  · intro i hi
    have hs := h1.saved i hi
    rw [hscr, add_ofNat_add] at hs
    rw [m3]
    show (s1.mem.writeW _ _).readW _ _ = _
    rw [add_ofNat_add, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), hs,
      hcs _ (savedRegs_preserved i hi)]
  · rw [m3]
    show (s1.mem.writeW _ _).readW _ _ = _
    rw [Mem.readW_writeW_self32, h1.gpr, hcs .lr (by decide)]
  · rw [m3, ← hm]
    show Frame _ s.mem (s1.mem.writeW _ _)
    have f1 := h1.frame
    rw [hscr] at f1
    refine (f1.sub fun r hr => ⟨P.scrR, by simp, ?_⟩).writeW (r := P.scrR) (by simp) _
      (Offset.contains_base _ (d := 2044) (by omega) (by omega))
    rw [List.mem_singleton] at hr; subst hr
    exact sub_scr (by omega)

/-- The prologue of `vg_mldsa_rej_ntt_poly`: `seed = r0`, `a = r1`,
`scratch = r2`. -/
theorem pro_rn (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = P.a) (h2 : σ.gpr .r2 = P.scr) (hprm : P.prm = 0)
    (hlen : P.len = 34) : WP isa (.block (pro .r2 .r1 (.imm 0) (.imm 34) .r0)) σ (J0 P σ) :=
  pro_ok hp rfl rfl rfl rfl (fun _ _ => rfl) h2 fun t ht => by
    run_block [ht, h0, h1, h2, hprm, hlen, and_self, and_true]

/-- The prologue of `vg_mldsa_rej_bounded_poly` and
`vg_mldsa_expand_mask_poly`: `seed = r0`, the parameter in `r1`, `a = r2`,
`scratch = r3`. -/
theorem pro_rb (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = P.prm) (h2 : σ.gpr .r2 = P.a) (h3 : σ.gpr .r3 = P.scr)
    (hlen : P.len = 66) : WP isa (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0)) σ (J0 P σ) :=
  pro_ok hp rfl rfl rfl rfl (fun _ _ => rfl) h3 fun t ht => by
    run_block [ht, h0, h1, h2, h3, hlen, and_self, and_true]

/-- The prologue of `vg_mldsa_sample_in_ball`: `ctilde = r0`, its length in
`r1`, `tau = r2`, `c = r3` and `scratch` the first stack argument, loaded
into `r12`. -/
theorem pro_ball (h0 : σ.gpr .r0 = P.sd) (h1 : σ.gpr .r1 = BitVec.ofNat 32 P.len) (h2 : σ.gpr .r2 = P.prm)
    (h3 : σ.gpr .r3 = P.a) (hs : stackArg σ 0 = P.scr)
    (hin : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4) :
    WP isa (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0)) σ (J0 P σ) := by
  rw [← List.singleton_append, WP.block_append_iff]
  have hin' : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 := hin
  have hs' : σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 0)) 32 = P.scr := hs
  refine WP.mono (Q := fun s => s = σ.setReg .r12 P.scr) (by
    apply WP.of_runBlock
    rw [runBlock_cons]
    simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32, hin', Option.map_some, hs',
      runStep_some, runBlock_nil]
    exact ⟨_, rfl, rfl⟩) fun s e => ?_
  subst e
  refine pro_ok hp rfl rfl rfl rfl (fun r hr => gpr_setReg_of_ne _ _ (ne_r12 hr)) (gpr_setReg_self _ _ _)
    fun t ht => ?_
  have g : ∀ r, r ≠ .r12 → t.gpr r = σ.gpr r := fun r hr => by rw [ht, gpr_setReg_of_ne _ _ hr]
  have g12 : t.gpr .r12 = P.scr := by rw [ht, gpr_setReg_self]
  have g0 := g .r0 (by decide)
  have g1 := g .r1 (by decide)
  have g2 := g .r2 (by decide)
  have g3 := g .r3 (by decide)
  run_block [g0, g1, g2, g3, g12, h0, h1, h2, h3, and_self, and_true]

end


/-! ## The epilogue -/

theorem preserved_saved : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, savedRegs.getD i .r4 = r := by decide

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The epilogue: our caller's registers restored, `r0` and the memory
unchanged. -/
theorem epi_ok {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.mem = s.mem ∧ s'.gpr .r0 = s.gpr .r0 := by
  have fs := hp.fscr
  unfold epi
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r3 P.scr) (by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil, he.r6]
    exact ⟨_, rfl, rfl⟩) fun s1 e1 => ?_
  subst e1
  have g3 : (s.setReg .r3 P.scr).gpr .r3 = P.scr := gpr_setReg_self _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 2012) (by decide) (by rw [g3]; omega)
    (g := σ.gpr) (by rw [g3]; exact he.sav) fun i hi => by
      rw [g3, add_ofNat_add]; exact inScrRd hp he (by omega)) fun s2 h2 => ?_
  have e3 : s2.gpr .r3 = P.scr := by rw [h2.other .r3 (by decide), g3]
  have ea : State.addr (s2.gpr .r3 + BitVec.ofNat 32 (2012 + 32)) = P.at' 2044 := by
    rw [e3]; exact at_eq hp (by decide)
  refine WP.mono (Q := fun s3 => s3 = s2.setReg .lr (s2.mem.readW (P.at' 2044) 32)) (by
    apply WP.of_runBlock
    rw [runBlock_cons, exec_ldr (by decide) (by rw [ea, h2.rd, h2.wr]; exact inScrRd hp he (by omega)),
      runStep_some, runBlock_nil, ea]
    exact ⟨_, rfl, rfl⟩) fun s3 e3' => ?_
  subst e3'
  refine ⟨⟨fun r hr => ?_, by rw [sp_setReg, h2.sp]; exact he.sp⟩, by rw [mem_setReg, h2.mem]; rfl, ?_⟩
  · by_cases e : r = .lr
    · subst e
      rw [gpr_setReg_self, h2.mem]; exact he.savlr
    · obtain ⟨i, hi, rfl⟩ := preserved_saved r hr e
      rw [gpr_setReg_of_ne _ _ e]; exact h2.loaded i hi
  · rw [gpr_setReg_of_ne _ _ (by decide), h2.other .r0 (by decide), gpr_setReg_of_ne _ _ (by decide)]

/-- The end of a sampling function that returns whether `j` (in `r2`) is 256. -/
theorem retEpi_ok {s : State} (he : Env P σ s) {j : Nat} (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j ≤ 256) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r0 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ abiPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.setReg .r0 (s.gpr .r2 >>> 8)) (by
    apply WP.of_runBlock
    set_option linter.unusedSimpArgs false in
    simp only [retJ, runBlock_cons, exec, Op2.eval, Option.map_some, runStep_some, runBlock_nil]
    exact ⟨_, rfl, rfl⟩) fun s1 e1 => ?_
  subst e1
  have he1 : Env P σ (s.setReg .r0 (s.gpr .r2 >>> 8)) :=
    he.regs ⟨fun r hr _ => gpr_setReg_of_ne _ _ (by rintro rfl; exact absurd hr (by decide)), rfl, rfl, rfl, rfl⟩
  refine WP.mono (epi_ok hp he1) fun s' ⟨ha, hm, h0⟩ => ⟨?_, hm, ha⟩
  rw [h0, gpr_setReg_self, hj, MlKem.Arm.Sample.ret_val hj']

/-- The end of a sampling function that returns nothing. -/
theorem epi_ok' {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => s'.mem = s.mem ∧ abiPreserved σ s' :=
  WP.mono (epi_ok hp he) fun _ h => ⟨h.2.1, h.1⟩

end

/-! ## Pieces of the loops -/

/-- The sign bit of `x - y`, compared with zero: `Z` is `y ≤ x`. -/
theorem sgn_z {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    ((x - y) >>> 31 - 0 == 0) = decide (y.toNat ≤ x.toNat) := by
  by_cases h : y.toNat ≤ x.toNat
  · have e : (x - y) >>> 31 = 0 := by bv_omega
    rw [e, decide_eq_true h]; rfl
  · have e : (x - y) >>> 31 = 1 := by bv_omega
    rw [e, decide_eq_false h]; rfl

/-- `r11 ← x - y`, its sign bit, compared with zero: `Z` is `y ≤ x`. -/
theorem sgn_ok (s : State) (x : Reg) (op : Op2) {y : BitVec 32} (hy : op.eval s = some y)
    (hx : (s.gpr x).toNat < 2 ^ 31) (hy' : y.toNat < 2 ^ 31) :
    WP isa (.block [.dp .sub .r11 x op, .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]) s fun s' =>
      s'.z = decide (y.toNat ≤ (s.gpr x).toNat) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e := sgn_z hx hy'
  apply WP.of_runBlock
  rw [runBlock_cons, show exec (.dp .sub .r11 x op) s = some (s.setReg .r11 (s.gpr x - y)) by
    simp only [exec, hy, Option.map_some], runStep_some]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, subFlags, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', e, and_self, and_true, true_and]
  exact fun r hr => by simp [hr]

/-- `jFull`: `Z` is `j ≥ 256`, for `j` (in `r2`) less than `2³¹`. -/
theorem jFull_ok (s : State) {j : Nat} (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j < 2 ^ 31) :
    WP isa (.block jFull) s fun s' =>
      s'.z = decide (256 ≤ j) ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ht : (s.gpr .r2).toNat = j := by rw [hj, toNat_ofNat32 (by omega)]
  refine WP.mono (sgn_ok s .r2 (.imm 256) (y := 256) rfl (by omega) (by decide)) fun s' h => ⟨?_, h.2⟩
  rw [h.1, ht]; rfl

/-- `step k`: `r0 ← r0 + k`, `r3 ← r3 - 1`, `Z` if it is zero. -/
theorem step_ok (s : State) {k : Nat} (ek : encodable (BitVec.ofNat 32 k) = true) :
    WP isa (.block (step k)) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 k ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧ s'.z = (s.gpr .r3 - 1 == 0) ∧
        (∀ r, r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  run_block [step, ek, and_self, and_true, true_and]
  exact fun r h0 h3 => by simp [h0, h3]

theorem shl2 (j : Nat) : BitVec.ofNat 32 j <<< 2 = BitVec.ofNat 32 (4 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem addr_aJ {j : Nat} (hj : j < 256) :
    State.addr (P.a + BitVec.ofNat 32 j <<< 2 + BitVec.ofNat 32 0) = coeffAddr P.A j := by
  rw [shl2]; exact addr_coeff hp.fa (by omega) hj

/-- `storeJ v`: `a[j] ← v`, `j ← j + 1`, for `j < 256` in `r2`. -/
theorem storeJ_ok {s : State} (he : Env P σ s) {v : Reg} (hv : v ≠ .r11) {j : Nat}
    (hj : s.gpr .r2 = BitVec.ofNat 32 j) (hj' : j < 256) :
    WP isa (.block (storeJ v)) s fun s' =>
      s'.mem = s.mem.writeW (coeffAddr P.A j) (s.gpr v) ∧ s'.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧
        (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.z = s.z ∧ Env P σ s' := by
  have ea := addr_aJ hp hj'
  have hin : InRegions s.wr (coeffAddr P.A j) 4 := by
    rw [he.wr, hp.wr]; exact ⟨P.aR, by simp, coeff_contains _ hj'⟩
  have hv' : ¬ v = .r11 := hv
  refine WP.mono (Q := fun s' : State => s'.mem = s.mem.writeW (coeffAddr P.A j) (s.gpr v) ∧
      s'.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z) ?_ fun s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2, he.step hp (rs := [P.aR]) (by
          rw [h.1]; exact (Frame.refl _ _).writeW (by simp) _ (coeff_contains _ hj'))
          (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
          (h.2.2.1 _ (by decide) (by decide)) (h.2.2.1 _ (by decide) (by decide)) h.2.2.2.1 h.2.2.2.2.1
          h.2.2.2.2.2.1⟩
  run_block [storeJ, hj, he.r5, ea, hin, hv', and_self, and_true, true_and]
  refine ⟨?_, fun r h2 h11 => ?_⟩
  · rw [BitVec.ofNat_add]; rfl
  · simp [h2, h11]

/-- Storing the next coefficient `x` of the list `L` stored at `a`. -/
theorem storeJ_stored {s : State} (he : Env P σ s) {v : Reg} (hv : v ≠ .r11) {L : List Zq}
    (hj : s.gpr .r2 = BitVec.ofNat 32 L.length) (hL : L.length < 256) (hst : Stored s.mem P.A L) {x : Zq}
    (hx : s.gpr v = zw x) :
    WP isa (.block (storeJ v)) s fun s' =>
      Stored s'.mem P.A (L ++ [x]) ∧ s'.gpr .r2 = BitVec.ofNat 32 (L ++ [x]).length ∧
        (∀ r, r ≠ .r2 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.z = s.z ∧ Env P σ s' ∧
        Frame [P.aR] s.mem s'.mem := by
  refine WP.mono (storeJ_ok hp he hv hj hL) fun s' ⟨hm, h2, hr, _, _, _, hz, he'⟩ => ⟨?_, ?_, hr, hz, he', ?_⟩
  · rw [hm, hx]; exact stored_snoc hst hL x
  · rw [h2, List.length_append, List.length_singleton]
  · rw [hm]; exact (Frame.refl _ _).writeW (by simp) _ (coeff_contains _ hL)

end


/-- `Env` after code that writes no memory and keeps `r5` and `r6`. -/
theorem Env.same {P : Sp} {σ s s' : State} (he : Env P σ s) (hm : s'.mem = s.mem) (g5 : s'.gpr .r5 = s.gpr .r5)
    (g6 : s'.gpr .r6 = s.gpr .r6) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Env P σ s' :=
  ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, g5.trans he.r5, g6.trans he.r6, by rw [hm]; exact he.sav,
    by rw [hm]; exact he.savlr, by rw [hm]; exact he.frame⟩

end VG.Proof.MlDsa.Arm.Sample
