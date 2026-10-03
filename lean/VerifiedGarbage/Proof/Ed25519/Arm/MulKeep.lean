import VerifiedGarbage.Proof.Ed25519.Arm.PointPowers
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep
import VerifiedGarbage.Impl.Ed25519.Arm.PointBatch
import VerifiedGarbage.Proof.Ed25519.Arm.BatchBits

/-! Merged from `Proof.Ed25519.Arm.PointPowersLoop`. -/
section
/-! Checkpoint-loop termination and exact table contents. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PowersInv (s₀ : State) (b : BitVec 32) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 (count - n)
  value : point (env s.mem b) 0 1 2 3 =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, tablePoint s.mem b (o + 128 * j) =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : PowersKeep b o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀)
    (hl : AllLim s₀.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (h11 : s₀.gpr .r11 = 0)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody o count batch) .ne) s₀ fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧
      PowersKeep b o (128 * count) s₀ t := by
  apply WP.loop (fun n => PowersInv s₀ b o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (powersBody_ok batch hi.ctx hi.lim o (count - (k + 1)) count hlo hbound
      (by omega) hn hi.counter ((hi.high 16 (by decide)).trans hd))
      fun t ⟨htc, htz, htl, htt, htv, hthi, htk⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have hv : point (env t.mem b) 0 1 2 3 =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [htv, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by
        cases batch <;> simp only [powerStride, Bool.false_eq_true, ite_true, ite_false] <;> omega)
    have ht : ∀ j < count - k, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases h : j < count - (k + 1)
      · rw [TableFrame.point htk.frame (by omega) (.inl (by omega)) (by omega) (by omega), hi.table j h]
      · have he : j = count - (k + 1) := by omega
        rw [he, htt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans (htk.mono (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, show count - (0 + 1) + 1 = count by omega,
        decide_true, Bool.not_true], htl, ht, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz,
        decide_eq_false (show count - (k + 1) + 1 ≠ count by omega), Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, hstep ▸ htc, hv, ht, hh, hkeep⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hc, hl, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact h11
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem pointPowers_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointPowers o count batch) s fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ PowersKeep b o (128 * count) s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hr : Rest [.r11] s t := ht.rest (by decide)
  refine WP.mono (powersLoop_ok batch (hc.of_rest hr (by decide)) (by rw [ht.mem]; exact hl)
    o count hlo hbound hn0 hn ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, htu, hv, hh, hu⟩ => ?_
  have hkeep : PowersKeep b o (128 * count) s t :=
    ⟨hr.mono (by decide), by rw [ht.mem]; exact Frame.refl _ _⟩
  rw [ht.mem] at htu hv hh
  exact ⟨hlu, htu, hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointBatch`. -/
section
/-! Merged from `Proof.Ed25519.Arm.AccumulateLoop`. -/
section
/-! The descending sixteen-bit loop follows the specification exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure AccumulateInv (s₀ : State) (b : BitVec 32) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat
  table : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)
  keep : LoopKeep b s₀ s

theorem accumulateLoop_ok {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (h11 : s₀.gpr .r11 = 16)
    (hb : ∀ i < 16, s₀.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop accumulateBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s₀ t := by
  apply WP.loop (AccumulateInv s₀ b start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok h.ctx h.lim k start scalar p hk h.counter
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tl, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat :=
      fun i hi => (tk.bit i hi).trans (h.bits i hi)
    have ht' : ∀ i < 16, tablePoint t.mem b (5696 + 128 * i) = powerPoint p (start + i) := by
      intro i hi
      exact (workspace_tablePoint tk.frame (by omega) (by omega)).trans (h.table i hi)
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, tz, decide_true, Bool.not_true], tl, tv, td, h.keep.trans tk⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, tz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.ctx h.ctx, tl, tc, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hc, hl, h11, hd, hp, hb, ht, LoopKeep.refl _ _⟩

theorem accumulate16_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point)
    (hb : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat)
    (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa accumulate16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s t := by
  refine WP.seq (wp_movw fun u hu => WP.block_nil ?_)
  have ku : LoopKeep b s u := LoopKeep.of_rest (hu.rest (ws := [.r11]) (by decide)) (by decide) hu.mem
  refine WP.mono (accumulateLoop_ok (ku.ctx hc) (by rw [hu.mem]; exact hl) start scalar p hu.gpr
    (by rw [hu.mem]; exact hb) (by rw [hu.mem]; exact hd) (by rw [hu.mem]; exact hp)
    (by rw [hu.mem]; exact ht)) fun t ⟨tl, tv, td, tk⟩ => ?_
  exact ⟨tl, tv, td, ku.trans tk⟩

end VG.Proof.Ed25519.Arm
end

/-! The local table preserves the accumulator and the checkpoint table. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.of_acc {b : BitVec 32} {o n : Nat} {s t : State} (h : AccKeep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩
theorem PowersKeep.of_keep {b : BitVec 32} {o n : Nat} {s t : State} (h : Keep b s t) :
    PowersKeep b o n s t := ⟨h.rest.mono (by decide), TableFrame.workspace h.frame⟩

theorem loadCheckpoint_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa loadCheckpoint s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b (1600 + 128 * j) ∧
      point (env t.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 1600 j (by omega) hj
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun t ⟨pt, lt, kt⟩ => ?_
  refine ⟨(AccKeep.of_keep ka).trans (ka'.trans (AccKeep.of_table kt (by decide) (by decide))), lt, ?_, ?_, ?_⟩
  · rw [pt, hm]
    exact workspace_tablePoint ka.frame (by omega) (by omega)
  · rw [point_congr (e := env t.mem b) (f := env a'.mem b) 17 18 19 20
      (kt.high 17 (by decide)) (kt.high 18 (by decide)) (kt.high 19 (by decide)) (kt.high 20 (by decide)),
      hm, ea, savePoint_eval]
  · rw [kt.high 16 (by decide), hm, ea, savePoint_d]

theorem prepareBatch_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (j : Nat) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => PowersKeep base 5696 2048 s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem base (5696 + 128 * i) =
        powerPoint (tablePoint s.mem base (1600 + 128 * j)) i) ∧ env t.mem base 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (loadCheckpoint_ok hc hl j hj h11) fun a ⟨ka, la, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (ka.ctx hc) la 5696 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨lb, bt, _, bh, kb⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨((PowersKeep.of_acc ka).trans kb).trans (PowersKeep.of_keep kt), lt, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval,
      point_congr (e := env b.mem base) (f := env a.mem base) 17 18 19 20
        (bh 17 (by decide)) (bh 18 (by decide)) (bh 19 (by decide)) (bh 20 (by decide)), av]
  · intro i hi
    have htab := bt i hi
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul] at htab
    exact (workspace_tablePoint kt.frame (by omega) (by omega)).trans
      (htab.trans (congrArg (fun p => powerPoint p i) ap))
  · rw [et, restorePoint_d, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.Arm
end

/-! Frames for scalar multiplication preserve argument pointers,
register saves, and all data beyond the compact tables. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev mulRegions (b : BitVec 32) (o n : Nat) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 32, 16⟩, ⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA b,
    ⟨State.addr b + BitVec.ofNat 64 o, n⟩]

structure MulKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame (mulRegions b o n) s.mem t.mem

theorem MulKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : MulKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem MulKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)
theorem MulKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : MulKeep b o n s t) (k : MulKeep b o n t u) : MulKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem MulKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : MulKeep b o' n' s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))), Offset.sub _ ho hn⟩
theorem MulKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) : MulKeep b o n s t :=
  ⟨h.rest, Frame.mono h.frame (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩
theorem MulKeep.of_loop {b : BitVec 32} {o n : Nat} {s t : State}
    (h : LoopKeep b s t) : MulKeep b o n s t :=
  ⟨h.rest.mono (by decide), h.frame.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [mulRegions, List.mem_cons, true_or, or_true])⟩
theorem MulKeep.of_bits {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)⟩
theorem MulKeep.of_rest {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem MulKeep.word {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192)
    (d : Nat) (hd : d = 48 ∨ d = 52) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem MulKeep.table {b : BitVec 32} {o n : Nat} {s t : State}
    (h : MulKeep b o n s t) {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192)
    (hn : o + n ≤ 8192) (hs : d + 128 ≤ o ∨ o + n ≤ d) :
    tablePoint t.mem b d = tablePoint s.mem b d := by
  refine tablePoint_frame h.frame fun r hr => ?_
  simp only [mulRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem smallFrame_env {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64) :
    env m' b = env m b := by
  funext i
  exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)))

theorem smallFrame_lim {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hl : AllLim m b) : AllLim m' b := by
  intro i k hk
  rw [limb_frame hf (fun r hr j hj => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk]
  exact hl i k hk

end VG.Proof.Ed25519.Arm
