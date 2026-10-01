import VerifiedGarbage.Proof.Ed25519.AArch64.CombStep

/-!
# The comb's loop

Untrusted. After step `c`, the accumulator represents `[v]B` for the partial
sum `v = combVal S c` (`CombDigits`); at `c = 64` that is the scalar.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64

/-- The loop's invariant, after `c` steps. -/
structure CombInv (s₀ : State) (base : Addr) (S c : Nat) (s : State) : Prop where
  bound : c ≤ 64
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 c
  d : env s.mem base 16 = Spec.Ed25519.d
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  value : Rep (point (env s.mem base) 0 1 2 3) (combVal S c • baseAff)
  keep : CombKeep base s₀ s

private theorem sub32_fact : ∀ c < 64,
    (BitVec.ofNat 64 c - BitVec.ofNat 64 32 == 0) = decide (c = 32) := by decide +kernel

private theorem next_fact : ∀ c < 64,
    BitVec.ofNat 64 c + BitVec.ofNat 64 1 = BitVec.ofNat 64 (c + 1) ∧
    (BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 64 != 0) = decide (c + 1 ≠ 64) := by decide +kernel

theorem combNext_ok (s : State) {c : Nat} (hc : c < 64) (h : s.gpr .x19 = BitVec.ofNat 64 c) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (c + 1) ∧ (t.gpr .x8 != 0) = decide (c + 1 ≠ 64) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 64 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact c hc).1, (next_fact c hc).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Before the even digits: four doublings and `[G]B`. -/
theorem combDoubling_ok {s : State} {base : Addr} (hs : Scr s base) {c : Nat} {v : ℤ}
    (hb : s.gpr .x19 = BitVec.ofNat 64 c) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hz : env s.mem base 21 = 0) (hv : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff))
    (hx : (s.gpr .x8 == 0) = decide (c = 32)) :
    WP isa (.ite (.zero .x .x8) (.seq double4 (.block combAddG)) (.block [])) s fun b =>
      Scr b base ∧ b.gpr .x19 = BitVec.ofNat 64 c ∧ env b.mem base 16 = Spec.Ed25519.d ∧
      env b.mem base 21 = 0 ∧
      Rep (point (env b.mem base) 0 1 2 3) ((if c = 32 then 16 * v + combGVal else v) • baseAff) ∧
      CombKeep base s b := by
  refine WP.ite (decide (c = 32)) (by simp only [eval, read_x, hx]) (fun hy => ?_) (fun hn => ?_)
  · have h32 : c = 32 := of_decide_eq_true hy
    refine WP.seq (WP.mono (double4_ok hs hd) fun b ⟨bp, bh, bk⟩ => ?_)
    have hsb := bk.scratch hs
    refine WP.mono (combAddG_ok hsb) fun e ⟨ke, ep, eh⟩ => ?_
    refine ⟨ke.scr hsb, (ke.gpr _ (by decide)).trans ((bk.gpr _ (by decide) (by decide)).trans hb),
      by rw [eh 16 (by decide), bh 16 (by decide)]; exact hd,
      by rw [eh 21 (by decide), bh 21 (by decide)]; exact hz, ?_,
      (CombKeep.of_double bk).trans (CombKeep.of_keep ke)⟩
    simp only [h32, ↓reduceIte]
    rw [ep, bp, ← zsmul_16]
    have h4 := powerPoint_rep hv 4
    rw [show (2 ^ 4 : Nat) = 16 from rfl] at h4
    exact pointAdd_rep h4 combG_ok
  · have h32 : c ≠ 32 := of_decide_eq_false hn
    exact WP.block_nil ⟨hs, hb, hd, hz, by simp only [h32, ↓reduceIte]; exact hv, CombKeep.refl _ _⟩

theorem combStep_ok {s₀ s : State} {base : Addr} {S c : Nat} (h : CombInv s₀ base S c s)
    (hc : c < 64) :
    WP isa combStep s fun t => (t.gpr .x8 != 0) = decide (c + 1 ≠ 64) ∧
      CombInv s₀ base S (c + 1) t := by
  rw [combStep]
  refine WP.seq (WP.mono (show WP isa (.block [.subImm .x .x8 .x19 32]) s fun t =>
      (t.gpr .x8 == 0) = decide (c = 32) ∧ Keeps [.x8] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (show 32 < 4096 by decide),
      read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, h.counter, sub32_fact c hc,
      Option.some.injEq, exists_eq_left']
    exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl,
      rfl⟩⟩) fun a ⟨az, ka⟩ => ?_)
  have hsa := h.scratch.of_keeps ka (by decide)
  have ea : env a.mem base = env s.mem base := by rw [ka.mem]
  refine WP.seq (WP.mono (combDoubling_ok (v := combVal S c) hsa ((ka.gpr _ (by decide)).trans h.counter)
    (by rw [ea]; exact h.d) (by rw [ea]; exact h.zero) (by rw [ea]; exact h.value) az)
    fun b ⟨hsb, b19, bd, bz, bv, kb⟩ => ?_)
  -- The digit's bit index.
  refine WP.seq (WP.mono (combIndex_ok b hsb hc b19) fun e ⟨e8, ke⟩ => ?_)
  have hse : Scr e base := hsb.of_keeps ke (by decide)
  have kab : CombKeep base s b := (CombKeep.of_keeps ka (by decide)).trans kb
  have bbits : ∀ q < 256, e.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [ke.mem, kab.bit hq]; exact h.bits q hq
  -- The nibble, its sign and magnitude, the masks and the table.
  have hn := nib_lt S (combIdx c)
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hse (combIdx_lt hc) e8 bbits) fun f ⟨f2, kf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok f hn f2) fun g ⟨g2, g1, kg⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combMasks_ok g (mag_lt hn) g2) fun i ⟨im, iz, ki⟩ => ?_
  have i19 : i.gpr .x19 = BitVec.ofNat 64 c := by
    rw [ki.gpr _ (by decide), kg.gpr _ (by decide), kf.gpr _ (by decide), ke.gpr _ (by decide), b19]
  refine WP.mono (combTableIdx_ok i hc i19) fun j ⟨j8, kj⟩ => ?_
  have hsj : Scr j base :=
    (((hse.of_keeps kf (by decide)).of_keeps kg (by decide)).of_keeps ki (by decide)).of_keeps kj
      (by decide)
  have jm : ∀ k, 1 ≤ k → k ≤ 8 → j.gpr (maskReg k) = mask (decide (mag (nib S (combIdx c)) = k)) :=
    fun k h1 h8 => by
      rw [kj.gpr _ (by
        have : ∀ k < 9, maskReg k ≠ .x8 := by decide
        simpa using this k (by omega))]
      exact im k h1 h8
  have jz : j.gpr .x22 = zeroBit (mag (nib S (combIdx c))) := by rw [kj.gpr _ (by decide)]; exact iz
  have j1 : j.gpr .x1 = mask (decide (nib S (combIdx c) < 8)) := by
    rw [kj.gpr _ (by decide), ki.gpr _ (by decide)]; exact g1
  have j19 : j.gpr .x19 = BitVec.ofNat 64 c := by rw [kj.gpr _ (by decide)]; exact i19
  have jmem : j.mem = b.mem := by rw [kj.mem, ki.mem, kg.mem, kf.mem, ke.mem]
  have kbj : CombKeep base b j :=
    ((((CombKeep.of_keeps ke (by decide)).trans (CombKeep.of_keeps kf (by decide))).trans
      (CombKeep.of_keeps kg (by decide))).trans (CombKeep.of_keeps ki (by decide))).trans
      (CombKeep.of_keeps kj (by decide))
  -- The entry.
  refine WP.seq (WP.mono (combSelectFrom_ok (List.range 32) (fun k hk => List.mem_range.mp hk) hsj
    (mag_lt hn) jm jz (List.mem_range.mpr (Nat.mod_lt _ (by decide))) (Nat.mod_lt _ (by decide)) j8)
    fun u ⟨uq, ku, ue⟩ => ?_)
  have hsu : Scr u base := ku.scr hsj
  -- Negated for a negative digit, and added.
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok hsu (sw := decide (nib S (combIdx c) < 8))
    (by rw [ku.gpr _ (by decide)]; exact j1)
    (by rw [ue 21 (by decide), jmem]; exact bz)) fun u' ⟨ku', uq', ue'⟩ => ?_
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry_ok (c % 32) (nib S (combIdx c)) (Nat.mod_lt _ (by decide)) hn
  have hcq : cachedIn (env u'.mem base) = cache q := by
    rw [uq', uq, ← hq]
    by_cases hlt : nib S (combIdx c) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  rw [WP.block_append_iff]
  refine WP.mono (pointAddMixed_ok (ku'.scr hsu) q hcq hqz) fun v ⟨kv, vp, vh⟩ => ?_
  have v19 : v.gpr .x19 = BitVec.ofNat 64 c := by
    rw [kv.gpr _ (by decide), ku'.gpr _ (by decide), ku.gpr _ (by decide)]; exact j19
  refine WP.mono (combNext_ok v hc v19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  have eu : ∀ x : Slot, (x.val < 4 ∨ 16 ≤ x.val) → env u'.mem base x = env b.mem base x :=
    fun x hx => by rw [ue' x (by omega), ue x (by omega), jmem]
  have kbt : CombKeep base b t :=
    (((kbj.trans (CombKeep.of_keep ku)).trans (CombKeep.of_keep ku')).trans (CombKeep.of_keep kv)).trans
      (CombKeep.of_keeps kt (by decide))
  have kst : CombKeep base s₀ t := (h.keep.trans kab).trans kbt
  refine ⟨by omega, (kab.trans kbt).scr h.scratch, t19, ?_, ?_, fun q hq => ?_, ?_, kst⟩
  · rw [kt.mem, vh 16 (by decide), eu 16 (by decide)]; exact bd
  · rw [kt.mem, vh 21 (by decide), eu 21 (by decide)]; exact bz
  · rw [(kab.trans kbt).bit hq]; exact h.bits q hq
  · have up : point (env u'.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by
      simp only [point, eu 0 (by decide), eu 1 (by decide), eu 2 (by decide), eu 3 (by decide)]
    rw [kt.mem, vp, up, ← combIdx_nib S c hc, add_smul, add_comm]
    exact pointAdd_rep bv hrq

/-! ## The loop -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      env t.mem base 21 = 0 ∧ point (env t.mem base) 0 1 2 3 = combG ∧
      t.gpr .x19 = BitVec.ofNat 64 0 := by
  rw [combInit, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d, .const 21 0] hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok (constPointOps combG) (ka.scr hs)) fun b ⟨kb, vb⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨(CombKeep.of_keep (ka.trans kb)).trans ⟨fun r hr _ _ => RegUpd.gpr_write_of_ne _ _ _ hr,
    rfl, rfl, rfl, Outside.refl _ _ _ _⟩, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.mem_write, vb, va]; rfl
  · simp only [RegUpd.mem_write, vb, va]; rfl
  · simp only [RegUpd.mem_write, vb, constPoint_eval]
  · rw [RegUpd.gpr_write_self]; rfl

theorem combMultiply_ok {s : State} {base : Addr} (hs : Scr s base) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hs) fun b ⟨kb, bd, bz, bp, b19⟩ => ?_)
  have init : CombInv s base S 0 b := by
    refine ⟨by decide, kb.scr hs, b19, bd, bz, fun q hq => ?_, ?_, kb⟩
    · rw [kb.bit hq]; exact hb q hq
    · rw [bp, combVal_zero, natCast_zsmul]; exact combG_ok
  apply WP.loop (fun n t => CombInv s base S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok ht (by omega)) fun u ⟨u8, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      refine Or.inl ⟨by simp only [eval, read_x, u8, show 64 - (0 + 1) + 1 = 64 from rfl, ne_eq,
        not_true_eq_false, decide_false], ?_, hu.keep⟩
      have hv := hu.value
      rw [show 64 - (0 + 1) + 1 = 64 from rfl, comb_sum hS, natCast_zsmul] at hv
      exact hv
    · refine Or.inr ⟨by simp only [eval, read_x, u8, show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨init, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64
