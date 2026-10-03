import VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad
import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.Arm.PointPowers
import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect
import VerifiedGarbage.Proof.Ed25519.Arm.Points

/-! Merged from `Proof.Ed25519.Arm.PointAccumulate`. -/
section
/-! Merged from `Proof.Ed25519.Arm.AccKeep`. -/
section
/-! Point accumulation changes the field workspace and its table pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev accClob : List Reg := .r12 :: clob
structure AccKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest accClob s t
  frame : Frame [FA b] s.mem t.mem

theorem AccKeep.ctx {b : BitVec 32} {s t : State} (h : AccKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem AccKeep.trans {b : BitVec 32} {s t u : State} (h : AccKeep b s t) (k : AccKeep b t u) :
    AccKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem AccKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem AccKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hws : ∀ r ∈ ws, r ∈ accClob) (hm : t.mem = s.mem) : AccKeep b s t :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem AccKeep.of_table {b : BitVec 32} {s t : State} {o n : Nat} (h : TableKeep b o n s t)
    (ho : 64 ≤ o) (hn : o + n ≤ 1600) : AccKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.high {b : BitVec 32} {s t : State} (h : TableKeep b 64 256 s t)
    (i : Slot) (hi : 4 ≤ i.val) :
    VG.Proof.Ed25519.Arm.env t.mem b i = VG.Proof.Ed25519.Arm.env s.mem b i :=
  congrArg VG.Proof.X25519.toFe (val16_congr (h.slot (by decide) i
    (.inr (by simp only [offset]; omega))))

theorem point_congr {e f : Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : point e x y z t = point f x y z t := by
  simp only [point, hx, hy, hz, ht]

theorem savePoint_d (e : Env) : evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : Env) : evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : Env) : evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : Env) :
    point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : Env) :
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl
theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PrepareAdd`. -/
section
/-! Save the accumulator and load the next exact power into Q. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem prepareAdd_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa prepareAdd s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 4 5 6 7 = tablePoint s.mem b (5696 + 128 * j) ∧
      point (env t.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (fieldCode_ok savePointOps hc hl) fun a ⟨ka, la, ea⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 5696 j (by omega) (by omega)
    ((ka.rest.gpr _ (by decide)).trans h11)) fun a' ⟨hptr, hr, hm⟩ => ?_
  have ka' : AccKeep b a a' := AccKeep.of_rest hr (by decide) hm
  refine WP.mono (pointFromTable_ok (ka'.ctx (ka.ctx hc)) (by rw [hm]; exact la)
    hptr (by omega) (by omega)) fun c ⟨pc, lc, kc⟩ => ?_
  have kc' : AccKeep b a' c := AccKeep.of_table kc (by decide) (by decide)
  have ks : AccKeep b s c := (AccKeep.of_keep ka).trans (ka'.trans kc')
  have savec : point (env c.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 := by
    rw [point_congr _ _ _ _ (kc.high 17 (by decide)) (kc.high 18 (by decide))
      (kc.high 19 (by decide)) (kc.high 20 (by decide)), hm, ea, savePoint_eval]
  have dc : env c.mem b 16 = env s.mem b 16 := by rw [kc.high 16 (by decide), hm, ea, savePoint_d]
  have tc : tablePoint a'.mem b (5696 + 128 * j) = tablePoint s.mem b (5696 + 128 * j) := by
    rw [hm]
    exact workspace_tablePoint ka.frame (by omega) (by omega)
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps (ks.ctx hc) lc) fun d ⟨kd, ld, ed⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kd.ctx (ks.ctx hc)) ld) fun t ⟨kt, lt, et⟩ => ?_
  refine ⟨ks.trans ((AccKeep.of_keep kd).trans (AccKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_q, ed, copyPointToQ_eval, pc, tc]
  · rw [et, restorePoint_saved, ed, copyPointToQ_saved, savec]
  · rw [et, restorePoint_d, ed, copyPointToQ_d, dc]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.BitMask`. -/
section
/-! Scalar bits in the sixteen-byte batch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem AccKeep.bit {b : BitVec 32} {s t : State} (h : AccKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1536)
    (.inl (by omega)) (by omega) (by decide)) _ (Region.contains_self _ _)


theorem scalarBitMask_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat) (hj : j < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t => AccKeep b s t ∧ t.mem = s.mem ∧
      t.gpr .r9 = 0 - BitVec.ofNat 32 (!bit).toNat := by
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have ep : s1.gpr .r2 = b + BitVec.ofNat 32 j := by
    rw [u1.gpr]
    change s.gpr .r0 + s.gpr .r11 = _
    rw [hc.r0, h11]
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (32 + j)) (by decide)
    (by rw [ep, Offset.add_add, addr_add (by have := hc.fit; omega)]; rw [Nat.add_comm j 32])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_
  have hr : Rest [.r2, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨AccKeep.of_rest hr (by decide) hm, hm, ?_⟩
  rw [u3.gpr]
  change s2.gpr .r9 - 1 = _
  rw [u2.gpr, u1.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointSelect`. -/
section
/-! Branch-free selection using the verified limb swaps. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def swapSlot (a b : Slot) (sw : Bool) (i : Slot) : Slot :=
  if sw then if i = a then b else if i = b then a else i else i

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env := fun i => e (swapSlot a b sw i)
def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapEnvs_step (ops : List (Slot × Slot)) (a b : Slot) (sw : Bool) {e f g : Env}
    (hf : f = swapEnv a b sw e) (hg : g = swapEnvs ops sw f) :
    g = swapEnvs ((a, b) :: ops) sw e := hg.trans (congrArg (swapEnvs ops sw) hf)

theorem swapField_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) (hab : a ≠ b) {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have ha := slot_range a
  have hb := slot_range b
  rw [ACC_eq] at ha hb
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok (by omega) (by omega) (by simp only [offset]; omega) hc
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ht => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr base) (offset i) k =
      limb s.mem (State.addr base) (offset (swapSlot a b sw i)) k := by
    intro i k hk
    by_cases hia : i = a
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.lx k hk
    by_cases hib : i = b
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, hia, sel, Bool.toNat_false, Bool.toNat_true, Nat.zero_ne_one] using ht.ly k hk
    · have hn1 : i.val ≠ a.val := fun h => hia (Fin.ext h)
      have hn2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
      have hi := slot_range i
      rw [ACC_eq] at hi
      have ei : swapSlot a b sw i = i := by simp only [swapSlot, hia, hib, ite_false, ite_self]
      rw [ei]
      refine limb_frame ht.frame (fun r hr j hj => ?_) k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (by simp only [offset]; omega) (by omega) (by omega)
  refine ⟨⟨ht.rest.mono (by decide), ?_⟩,
    fun i k hk => by rw [he i k hk]; exact hl _ k hk,
    ht.rest.gpr _ (by decide), funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (he i))⟩
  refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)

theorem swapFields_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (ops : List (Slot × Slot)) (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool}
    (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (swapFields ops)) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl, rfl⟩
  | cons ab ops ih =>
    rcases ab with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc hl a b (hops (a, b) (by simp)) hm) fun t ⟨hk, hlt, ht9, hv⟩ => ?_
    refine WP.mono (ih (hk.ctx hc) hlt (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (ht9.trans hm))
      fun u ⟨ku, hlu, hu9, vu⟩ => ?_
    refine ⟨hk.trans ku, hlu, hu9.trans ht9, ?_⟩
    exact swapEnvs_step ops a b sw (e := env s.mem base) (f := env t.mem base) (g := env u.mem base) hv vu

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by cases sw <;> rfl

theorem pointSelect_d (e : Env) (sw : Bool) : swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block pointSelect) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 =
        (if sw then point (env s.mem base) 17 18 19 20 else point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.mono (swapFields_ok hc hl pointSelectPairs (by decide) hm) fun t ⟨hk, hlt, _, hv⟩ => ?_
  exact ⟨hk, hlt, by rw [hv, pointSelect_eval], by rw [hv, pointSelect_d]⟩

end VG.Proof.Ed25519.Arm
end

/-! Add one exact table power and select with its scalar bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem select_flip {α : Type} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) : c = if bit then b else a := by
  cases bit with
  | false => exact hc.trans hd
  | true => exact hc.trans he

theorem pointAccumulate_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem b 16 = Spec.Ed25519.d) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa pointAccumulate s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3)
          (tablePoint s.mem b (5696 + 128 * j)) else point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (prepareAdd_ok hc hl j hj h11) fun u ⟨ku, lu, up, uq, us, ud⟩ => ?_)
  refine WP.seq (WP.mono (pointAdd_ok (ku.ctx hc) lu (ud.trans hd)) fun v ⟨kv, lv, vp, vh⟩ => ?_)
  have ks := ku.trans (AccKeep.of_keep kv)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := (ks.rest.gpr _ (by decide)).trans h11
  have hvb : v.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat :=
    (ks.bit j hj).trans hbit
  have vs : point (env v.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 :=
    (point_congr (e := env v.mem b) (f := env u.mem b) 17 18 19 20 (vh 17 (by decide)) (vh 18 (by decide))
      (vh 19 (by decide)) (vh 20 (by decide))).trans us
  have vp' : point (env v.mem b) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (tablePoint s.mem b (5696 + 128 * j)) :=
    vp.trans (congrArg₂ Spec.Ed25519.pointAdd up uq)
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (ks.ctx hc) j hj hvc bit hvb) fun w ⟨kw, mw, mask⟩ => ?_
  refine WP.mono (pointSelect_ok (kw.ctx (ks.ctx hc)) (by rw [mw]; exact lv) mask)
    fun t ⟨kt, lt, tp, td⟩ => ?_
  refine ⟨ks.trans (kw.trans (AccKeep.of_keep kt)), lt, ?_, ?_⟩
  · exact select_flip bit tp
      ((congrArg (fun m => point (env m b) 17 18 19 20) mw).trans vs)
      ((congrArg (fun m => point (env m b) 0 1 2 3) mw).trans vp')
  · exact td.trans ((congrArg (fun m => env m b 16) mw).trans ((vh 16 (by decide)).trans ud))

end VG.Proof.Ed25519.Arm
end

/-! One descending scalar bit implements the specification's recursion. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [scalarBit, h] <;> decide

theorem choose_after (s n : Nat) (p x y : Spec.Ed25519.Point)
    (hx : x = after s p (n + 1)) (hy : y = powerPoint p n) :
    (if scalarBit s n then Spec.Ed25519.pointAdd x y else x) = after s p n := by
  rw [hx, hy]
  have h := (after_step s p n).symm
  by_cases hz : (s / 2 ^ n) % 2 = 0
  · simpa only [scalarBit, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, ite_true] using h
  · simpa only [scalarBit, hz, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] using h

abbrev loopClob : List Reg := .r11 :: accClob
structure LoopKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest loopClob s t
  frame : Frame [FA b] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (s : State) : LoopKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem LoopKeep.ctx {b : BitVec 32} {s t : State} (h : LoopKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem LoopKeep.trans {b : BitVec 32} {s t u : State} (h : LoopKeep b s t) (k : LoopKeep b t u) :
    LoopKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem LoopKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : LoopKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩
theorem LoopKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (hr : Rest ws s t)
    (hw : ∀ r ∈ ws, r ∈ loopClob) (hm : t.mem = s.mem) : LoopKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem LoopKeep.bit {b : BitVec 32} {s t : State} (h : LoopKeep b s t) (j : Nat) (hj : j < 16) :
    t.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) := by
  refine h.frame _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact (Offset.disjoint (State.addr b) (d := 32 + j) (n := 1) (e := 64) (k := 1536)
    (.inl (by omega)) (by omega) (by decide)) _ (Region.contains_self _ _)

theorem accumulateDec_ok (s : State) (n : Nat) (h11 : s.gpr .r11 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block [.dp .sub .r11 .r11 (.imm 1)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 n ∧ Rest [.r11] s t ∧ t.mem = s.mem := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨?_, ht.rest (by decide), ht.mem⟩
  rw [ht.gpr]
  change s.gpr .r11 - 1 = _
  rw [h11, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem accumulateTest_ok (s : State) (n : Nat) (hn : n < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 n) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun t => t.z = decide (n = 0) ∧
      Rest [] s t ∧ t.mem = s.mem := by
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨?_, ht.rest _, ht.mem⟩
  have he : BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n := BitVec.sub_zero _
  rw [hz, h11, he, ofNat_beq_zero (by omega)]

theorem accumulateBody_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 (n + 1))
    (hb : s.mem (State.addr b + BitVec.ofNat 64 (32 + n)) = BitVec.ofNat 8 (scalarBit scalar (start + n)).toNat)
    (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem b (5696 + 128 * n) = powerPoint p (start + n)) :
    WP isa accumulateBody s fun t => t.gpr .r11 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      AllLim t.mem b ∧ point (env t.mem b) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ LoopKeep b s t := by
  refine WP.seq (WP.mono (accumulateDec_ok s n h11) fun u ⟨uc, ur, um⟩ => ?_)
  have uk : LoopKeep b s u := LoopKeep.of_rest ur (by decide) um
  refine WP.seq (WP.mono (pointAccumulate_ok (uk.ctx hc) (by rw [um]; exact hl) n hn uc
    (by rw [um]; exact hd) (scalarBit scalar (start + n)) (by rw [um]; exact hb))
    fun v ⟨vk, vl, vp, vd⟩ => ?_)
  have vc := (vk.rest.gpr .r11 (by decide)).trans uc
  have vpoint : point (env v.mem b) 0 1 2 3 = after scalar p (start + n) :=
    vp.trans (choose_after scalar (start + n) p _ _
      ((congrArg (fun m => point (env m b) 0 1 2 3) um).trans hp)
      ((congrArg (fun m => tablePoint m b (5696 + 128 * n)) um).trans ht))
  refine WP.mono (accumulateTest_ok v n hn vc) fun t ⟨tz, tr, tm⟩ => ?_
  exact ⟨(tr.gpr _ (by decide)).trans vc, tz, tm ▸ vl,
    (congrArg (fun m => point (env m b) 0 1 2 3) tm).trans vpoint,
    (congrArg (fun m => env m b 16) tm).trans (vd.trans ((congrArg (fun m => env m b 16) um).trans hd)),
    uk.trans ((LoopKeep.of_acc vk).trans (LoopKeep.of_rest tr (by decide) tm))⟩

end VG.Proof.Ed25519.Arm
