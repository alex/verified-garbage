import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Double
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop

/-!
# Ed25519 doublings with AVX512_IFMA: four of them

Untrusted: everything here is checked by Lean. `Ifma.double4` loads slots
0–3 into the lanes, doubles them four times (`vdbl_wp`) and stores them
back: the point in slots 0–3 then represents `16a` if it represented `a`.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519 VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord mul4 carry)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds EnvOK symOf symOf_eq lanes slotv CConsts carryNat fe5 fe5_congr
  fe5_carry carryI_wp vm vm_gpr vm_rd vm_wr envOK_of envOf envOf_m lt64 run_ok stores_mq stores_outside nat_ok
  mq mq_eq_word packW packW_val carryNat_le limbNat limbNat_lv consts_wp cregs)
open VG.Proof.X25519.X86_64 (Outside word val4 fe F clob Keeps)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## Storing -/

theorem packB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hk : EConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ 2 ^ 51 + 18) : EnvOK s packB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [packB]
    split
    · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; exact this
    · exact lt64 _
  · simp only [packB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k13 l hl]
      · split
        · subst_vars; rw [hk.k26 l hl]
        · split
          · subst_vars; rw [hk.k39 l hl]
          · exact lt64 _

/-- `vstore`: each lane as four words, in slots 0–3. -/
theorem vstore_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : EConsts s.mem base) (hy : Small s) :
    WP isa (.block vstore) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 64 128 s.mem s'.mem ∧ ∀ m < 4, F s'.mem base (64 + 32 * m) = fe5 (lanes s 0 m) := by
  rw [vstore_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (carryI_wp hs hc hk.toCConsts fun l hl i hi => by have := hy l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ : s₁.gpr .rdi = base := by rw [vm_gpr v₁]; exact hs
  have hc₁ : VG.Proof.X25519.X86_64.Ifma.Ctx s₁ := by intro d hd; rw [vm_gpr v₁, vm_wr v₁]; exact hc d hd
  have hk₁ : EConsts s₁.mem base := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁ hc₁ hk₁.toCConsts fun l hl i hi => by have := (u₁ l hl i hi).2; omega)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [vm_gpr v₂]; exact hs₁
  have hc₂ : VG.Proof.X25519.X86_64.Ifma.Ctx s₂ := by intro d hd; rw [vm_gpr v₂, vm_wr v₂]; exact hc₁ d hd
  have hk₂ : EConsts s₂.mem base := by rw [m₂]; exact hk₁
  have b₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i ≤ 2 ^ 51 + 18 := fun l hl i hi => by
    rw [(u₂ l hl i hi).1]; exact carryNat_le _ (fun j hj => (u₁ l hl j hj).2) i hi
  have hE := packB_env hs₂ hk₂ b₂
  have e : Sym.init.run vpackE = some packS := symOf_eq _ _
  refine WP.mono (run_ok hc₂ e) fun s₃ h => ?_
  have v₃ : vm s₂ s₃ = s₃ := h.eq
  refine ⟨(vm_gpr v₃).trans ((vm_gpr v₂).trans (vm_gpr v₁)), (vm_rd v₃).trans ((vm_rd v₂).trans (vm_rd v₁)),
    (vm_wr v₃).trans ((vm_wr v₂).trans (vm_wr v₁)), ?_, fun m hm => ?_⟩
  · rw [h.mem, hs₂, m₂, m₁]
    exact stores_outside _ _ _ (by decide) _ (by decide +kernel)
  · have w : ∀ j < 4, (word s₃.mem base (64 + 32 * m + 8 * j)).toNat =
        packW (fun i => lanes s₂ 0 m i) (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) j := fun j hj => by
      rw [← mq_eq_word, h.mem, hs₂, stores_mq _ _ _ _ (packT_mem m hm) hj packS_small packS_apart,
        (nat_ok hE _ hj (packT_ok m hm j hj)).1, packT_nat _ m hm j hj, envOf_m hs₂, envOf_m hs₂,
        envOf_m hs₂, envOf_m hs₂, hk₂.km m hm, hk₂.k13 m hm, hk₂.k26 m hm, hk₂.k39 m hm]
      rfl
    have fe' : fe s₃.mem base (64 + 32 * m) = VG.Proof.X25519.X86_64.Ifma.lv (lanes s₂ 0 m) := by
      simp only [fe, val4]
      have w0 := w 0 (by decide); have w1 := w 1 (by decide); have w2 := w 2 (by decide)
      have w3 := w 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
      rw [w0, show 64 + 32 * m + 16 = 64 + 32 * m + 8 * 2 by rfl, w2, w1, w3]
      exact packW_val _ (b₂ m hm)
    show VG.Proof.X25519.toFe _ = _
    rw [fe']
    rw [show VG.Proof.X25519.toFe (VG.Proof.X25519.X86_64.Ifma.lv (lanes s₂ 0 m)) = fe5 (lanes s₂ 0 m) from rfl,
      fe5_congr (fun i hi => (u₂ m hm i hi).1), fe5_carry _ (by have := (u₁ m hm 4 (by decide)).2; omega),
      fe5_congr (fun i hi => (u₁ m hm i hi).1), fe5_carry _ (by have := hy m hm 4 (by decide); omega)]

/-! ## Before the loop -/

theorem fe5_load (m : Mem) (base : Addr) (l : Nat) :
    fe5 (limbNat (fun k => (mq m base (64 + 32 * l + 8 * k)).toNat) (2 ^ 51 - 1)) = F m base (64 + 32 * l) := by
  show VG.Proof.X25519.toFe _ = VG.Proof.X25519.toFe _
  rw [limbNat_lv _ (fun k _ => BitVec.isLt _)]
  rfl

theorem ctx_of {s : State} {base : Addr} (hs : Scratch s base) : VG.Proof.X25519.X86_64.Ifma.Ctx s :=
  fun d hd => by
    rw [hs.rdi]
    exact ⟨_, hs.wr, Offset.contains_base base (show d + 32 ≤ 8192 by omega) (by omega)⟩

theorem mov32_wp (s : State) (r : Reg) (n : BitVec 32) :
    WP isa (.block [.mov32 r (.imm n)]) s fun t => t.gpr r = n.setWidth 64 ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ x l, qw t x l = qw s x l := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q hq => by simp only [hq, ite_false], rfl, rfl, rfl, fun _ _ => rfl⟩

theorem dec_wp (s : State) (n : Nat) (hn : n < 16) (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rsi (.imm 1)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧ Keeps [.rsi] s t ∧
      ∀ x l, qw t x l = qw s x l := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    hc, point_counter_zero n hn, e, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem lanes_qw {s t : State} (h : ∀ x l, qw t x l = qw s x l) (r : Nat) : lanes t r = lanes s r := by
  funext l i; simp only [lanes, h]

theorem lanePt_qw {s t : State} (h : ∀ x l, qw t x l = qw s x l) : lanePt t = lanePt s := by
  simp only [lanePt, lanes_qw h]

theorem cregs_clob : ∀ r ∈ cregs, r ∈ clob := by decide

theorem prep_wp {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ ([.mov32 .rsi (.imm 4)] : List Instr))) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rsi = BitVec.ofNat 64 4 ∧ (∀ r, r ∉ clob → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 1664 224 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧
      lanePt t = point (env s.mem base) 0 1 2 3 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (consts_wp s) fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₁, m₁, rd₁, wr₁, _, _, _⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vload_wp hs₁.rdi (ctx_of hs₁) ha hc hd hb h8 h9 h10) fun s₂ ⟨g₂, rd₂, wr₂, o₂, k₂, u₂⟩ => ?_
  refine WP.mono (mov32_wp s₂ .rsi 4) fun t ⟨tr, tg, tm, trd, twr, tq⟩ => ?_
  have hl := lanes_qw tq 0
  refine ⟨by rw [tg _ (by decide), g₂]; exact hs₁.rdi, tr, fun r hr hr' => ?_, by rw [trd, rd₂, rd₁],
    by rw [twr, wr₂, wr₁], by rw [tm, ← m₁]; exact o₂, by rw [tm]; exact k₂,
    fun l hl' i hi => by rw [hl]; have := (u₂ l hl' i hi).2; omega, ?_⟩
  · rw [tg _ hr', g₂, g₁ r (fun h => hr (cregs_clob r h))]
  · have e : ∀ l (hl' : l < 4), fe5 (lanes t 0 l) = env s.mem base ⟨l, by omega⟩ := fun l hl' => by
      rw [hl, fe5_congr (fun i hi => (u₂ l hl' i hi).1), fe5_load, m₁]; rfl
    simp only [lanePt, point]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    rfl

/-! ## Four doublings -/

/-- The loop's invariant, with `n` doublings left. -/
structure LoopInv (s : State) (base : Addr) (a : EPoint dZ) (n : Nat) (t : State) : Prop where
  pos : 0 < n
  le : n ≤ 4
  rdi : t.gpr .rdi = base
  rsi : t.gpr .rsi = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ clob → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 1024 864 s.mem t.mem
  consts : EConsts t.mem base
  small : Small t
  rep : Rep (lanePt t) ((2 ^ (4 - n) : Nat) • a)

theorem LoopInv.ctx {s : State} {base : Addr} {a : EPoint dZ} {n : Nat} {t : State} (hs : Scratch s base)
    (h : LoopInv s base a n t) : VG.Proof.X25519.X86_64.Ifma.Ctx t :=
  ctx_of ⟨h.rdi, by rw [h.wr]; exact hs.wr, hs.nowrap⟩

theorem double4_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa VG.Impl.Ed25519.X86_64.Ifma.double4 s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : VG.Impl.Ed25519.X86_64.Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧
      (∀ r, r ∉ clob → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 64 1824 s.mem t.mem := by
  rw [VG.Impl.Ed25519.X86_64.Ifma.double4]
  refine WP.seq (WP.mono (prep_wp hs) fun s₁ ⟨r₁, c₁, g₁, rd₁, wr₁, o₁, k₁, sm₁, p₁⟩ => ?_)
  refine WP.seq ?_
  refine WP.loop (LoopInv s base a) (fun n t h => ?_) 4 s₁
    ⟨by decide, by decide, r₁, c₁, g₁, rd₁, wr₁, o₁.mono (by decide) (by decide), k₁, sm₁,
      by rw [p₁]; simpa using ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.pos; omega : n ≠ 0)
  rw [WP.block_append_iff]
  refine WP.mono (vdbl_wp h.rdi (h.ctx hs) h.consts h.small) fun u ⟨ug, urd, uwr, uo, usm, up⟩ => ?_
  refine WP.mono (dec_wp u k (by have := h.le; omega) (by rw [ug]; exact h.rsi)) fun w ⟨wc, wz, kw, wq⟩ => ?_
  have wr' : w.gpr .rdi = base := by rw [kw.1 _ (by decide), ug]; exact h.rdi
  have wg : ∀ r, r ∉ clob → r ≠ .rsi → w.gpr r = s.gpr r := fun r hr hr' => by
    rw [kw.1 _ (by simpa using hr'), ug]; exact h.gpr r hr hr'
  have wrd : w.rd = s.rd := by rw [kw.2.2.1, urd]; exact h.rd
  have wwr : w.wr = s.wr := by rw [kw.2.2.2, uwr]; exact h.wr
  have wm : Outside base 1024 864 s.mem w.mem := by
    rw [kw.2.1]; exact h.mem.trans (uo.mono (by decide) (by decide))
  have wk : EConsts w.mem base := by rw [kw.2.1]; exact h.consts.outside uo
  have wsm : Small w := by intro l hl i hi; rw [lanes_qw wq]; exact usm l hl i hi
  have wp : Rep (lanePt w) ((2 ^ (4 - k) : Nat) • a) := by
    rw [lanePt_qw wq, up, show 4 - k = (4 - (k + 1)) + 1 by have := h.le; omega, pow_succ, mul_nsmul,
      two_nsmul]
    exact dblPoint_rep h.rep.proj
  by_cases hk : k = 0
  · subst hk
    refine Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], ?_⟩
    have hsw : Scratch w base := ⟨wr', by rw [wwr]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (vstore_wp wr' (ctx_of hsw) wk wsm) fun t ⟨tg, trd, twr, tou, tf⟩ => ?_
    have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
      simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
      rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide)]
      rfl
    refine ⟨by rw [pt]; exact wp, fun i hi => ?_, fun r hr hr' => by rw [tg]; exact wg r hr hr',
      by rw [trd]; exact wrd, by rw [twr]; exact wwr, wm.mono (by decide) (by decide) |>.trans
        (tou.mono (by decide) (by decide))⟩
    have := i.isLt
    simp only [env, VG.Impl.Ed25519.X86_64.offset]
    rw [Outside_F tou (by omega) (Or.inr (by omega)), Outside_F wm (by omega) (Or.inl (by omega))]
  · refine Or.inr ⟨by simp only [eval, wz, decide_eq_false hk, Option.map_some, Bool.not_false],
      k, by omega, by omega, by have := h.le; omega, wr', wc, wg, wrd, wwr, wm, wk, wsm, wp⟩

end VG.Proof.Ed25519.X86_64.Ifma
