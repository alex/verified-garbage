import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Impl.Ed25519.X86.PointSelect
import VerifiedGarbage.Proof.Ed25519.X86.Points

/-! Merged from `Proof.Ed25519.X86.PointAccumulate`. -/
section
/-! Merged from `Proof.Ed25519.X86.BitMask`. -/
section
/-! Only public counters determine the address of a secret scalar bit. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.word {x : BitVec 32} {s t : State} (h : FieldKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem FieldKeep.bit {x : BitVec 32} {s t : State} (h : FieldKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 64 864)) _ (Region.contains_self _ _)

theorem scalarBitMask_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t =>
      FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .ecx = mask (!bit).toNat := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_movi fun b hb' => wp_mul fun c hmul => ?_
  refine Wp.wp_add fun d hd _ => Wp.wp_add fun e he _ => ?_
  have pk : Keep s e := (updKeep ha).trans ((updKeep hb').trans (hmul.keep.trans
    ((updKeep hd).trans (updKeep he))))
  have pc : c.gpr .eax = BitVec.ofNat 32 (16 * batch) := by
    apply BitVec.eq_of_toNat_eq
    change v c .eax = _
    rw [hmul.eax]
    simp only [v, hb'.other .eax (by decide), ha.gpr, hb'.gpr]
    change (wd s.mem x 28).toNat * 16 % 2 ^ 32 = _
    rw [hbv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show batch < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm batch 16)
  have pe : addr (e.gpr .eax) 7168 = addr x (7168 + (16 * batch + j)) := by
    rw [he.gpr, hd.gpr, pc, hmul.other .esi (by decide) (by decide),
      hb'.other .esi (by decide), ha.other .esi (by decide), hjv,
      hd.other .edi (by decide), hmul.other .edi (by decide) (by decide),
      hb'.other .edi (by decide), ha.other .edi (by decide), hc.edi]
    rw [← BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 32 (16 * batch + j)) x, addr_plus,
      Nat.add_comm (16 * batch + j) 7168]
  refine scalar_ld8 pe ((pk.ctx hc).inRW (by omega) (by decide)) fun f hf =>
    Wp.wp_subi fun g hg _ _ => WP.block_nil ?_
  have km : g.mem = s.mem := by rw [hg.mem, hf.mem, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem (pk.trans ((updKeep hf).trans (updKeep hg))) km, km, ?_⟩
  rw [hg.gpr, hf.gpr, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointSelect`. -/
section
/-! Field and point selection by a fixed sequence of masked swaps. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapsEnv (pairs : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  pairs.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a b : Slot) (hab : a ≠ b)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (VG.Impl.X25519.X86.cswap (offset a) (offset b))) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapEnv a b sw (env s.mem x) := by
  have sep := slot_ne (slot_valid b) (slot_valid a) (fun h => hab (offset_inj h))
  refine WP.mono (cswap_ok hc (slot_below (slot_valid a)) (slot_below (slot_valid b)) sep
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ⟨hk, hm', hf, ha, hb⟩ => ?_
  have wide : Frame [sub x 64 864] s.mem t.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 64 864, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
    · exact sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
  refine ⟨⟨hk, wide⟩, hm', ?_⟩
  have hfit := hc.fit
  funext i
  by_cases hia : i = a
  · subst i
    rw [swapEnv, Function.update_of_ne hab, Function.update_self]
    change VG.Proof.X25519.toFe (fe t.mem x (offset a)) = _
    rw [ha]
    cases sw <;> rfl
  · by_cases hib : i = b
    · subst i
      rw [swapEnv, Function.update_self]
      change VG.Proof.X25519.toFe (fe t.mem x (offset b)) = _
      rw [hb]
      cases sw <;> rfl
    · rw [swapEnv, Function.update_of_ne hib, Function.update_of_ne hia]
      apply congrArg VG.Proof.X25519.toFe
      apply fe_frame
      intro k hk'
      apply wd_frame hf
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hs := slot_ne (slot_valid a) (slot_valid i) (fun h => hia (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])
      · have hs := slot_ne (slot_valid b) (slot_valid i) (fun h => hib (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])

theorem swapsEnv_step (pairs : List (Slot × Slot)) (a b : Slot) (sw : Bool)
    {e f g : Env} (h : f = swapEnv a b sw e) (k : g = swapsEnv pairs sw f) :
    g = swapsEnv ((a, b) :: pairs) sw e := by
  rw [k, h]; rfl

theorem swapFields_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (pairs : List (Slot × Slot)) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (swapFields pairs)) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapsEnv pairs sw (env s.mem x) := by
  induction pairs generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl, rfl⟩
  | cons pair pairs ih =>
    rcases pair with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc a b (hpairs _ List.mem_cons_self) sw hm) fun t ⟨kt, mt, et⟩ => ?_
    refine WP.mono (ih (kt.ctx hc) (fun p hp => hpairs p (List.mem_cons_of_mem _ hp)) (mt.trans hm))
      fun u ⟨ku, mu, eu⟩ => ?_
    exact ⟨kt.trans ku, mu.trans mt, swapsEnv_step pairs a b sw et eu⟩

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by
  cases sw <;> rfl

theorem pointSelect_high (e : Env) (sw : Bool) :
    swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e 16 = e 16 := rfl

theorem pointSelect_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (sw : Bool)
    (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block pointSelect) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 =
        (if sw then point (env s.mem x) 17 18 19 20 else point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = env s.mem x 16 := by
  refine WP.mono (swapFields_ok hc _ (by decide) sw hm) fun t ⟨hk, _, he⟩ => ?_
  rw [he]
  exact ⟨hk, pointSelect_eval _ _, pointSelect_high _ _⟩

end VG.Proof.Ed25519.X86
end

/-! One exact scalar-multiplication bit, including masked selection. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem select_flip {α : Sort _} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) :
    c = if bit then b else a := by
  cases bit <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hd, he] using hc

theorem pointAccumulate_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block pointAccumulate) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3)
          (tablePoint s.mem x (5120 + 128 * j)) else point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  simp only [pointAccumulate, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (prepareAdd_ok hc j hj hjv) fun u ⟨ku, pu, qu, su, du⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAdd_ok (ku.ctx hc) (du.trans hd)) fun v ⟨kv, pv, hv⟩ => ?_
  have kp := ku.trans kv
  have va := pv.trans (congrArg₂ Spec.Ed25519.pointAdd pu qu)
  have vs : point (env v.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 :=
    (point_congr _ _ _ _ (hv 17 (by decide)) (hv 18 (by decide))
      (hv 19 (by decide)) (hv 20 (by decide))).trans su
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (kp.ctx hc) batch j hb hj
    ((kp.word hc 28 (by decide)).trans hbv) (kp.keep.esi.trans hjv) bit
    ((kp.bit hc _ (by omega)).trans hbit)) fun w ⟨kw, mw, bw⟩ => ?_
  refine WP.mono (pointSelect_ok (kw.ctx (kp.ctx hc)) (!bit) bw) fun t ⟨kt, pt, dt⟩ => ?_
  refine ⟨kp.trans (kw.trans kt), ?_, ?_⟩
  · exact select_flip bit pt (by rw [mw]; exact vs) (by rw [mw]; exact va)
  · rw [dt, mw, hv 16 (by decide), du, hd]

end VG.Proof.Ed25519.X86
end

/-! Descending bits follow the exact pointMul recursion. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

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

theorem IKeep.word {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem IKeep.bit {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 64 864)) _ (Region.contains_self _ _)

theorem accumulateBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (n batch scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hb : batch < 32)
    (hindex : wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s.gpr .esi = BitVec.ofNat 32 (n + 1))
    (hbit : s.mem (addr x (7168 + (16 * batch + n))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + n)).toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d)
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n + 1))
    (ht : tablePoint s.mem x (5120 + 128 * n) = powerPoint p (16 * batch + n)) :
    WP isa (.block accumulateBody) s fun t =>
      IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      isa.eval .ne t = some (!decide (n = 0)) ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch + n) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  simp only [accumulateBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine Wp.wp_subi fun u hu _ _ => WP.block_nil ?_
  have ku : IKeep x s u := IKeep.of_counter hu
  have bu : u.gpr .esi = BitVec.ofNat 32 n := by
    rw [hu.gpr, hcounter]
    exact (Wp.ofNat_pred (by omega)).trans (congrArg (BitVec.ofNat 32) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (pointAccumulate_ok (ku.ctx hc) batch n hb hn
    (by rw [hu.mem]; exact hindex) bu (scalarBit scalar (16 * batch + n))
    (by rw [hu.mem]; exact hbit) (by rw [hu.mem]; exact hd)) fun v ⟨kv, pv, dv⟩ => ?_
  have bv := kv.keep.esi.trans bu
  have vp : point (env v.mem x) 0 1 2 3 = after scalar p (16 * batch + n) :=
    pv.trans (choose_after scalar (16 * batch + n) p _ _
      ((congrArg (fun m => point (env m x) 0 1 2 3) hu.mem).trans hp)
      ((congrArg (fun m => tablePoint m x (5120 + 128 * n)) hu.mem).trans ht))
  refine Wp.wp_test fun t kt zt => WP.block_nil ?_
  have keep : Keep v t := ⟨by rw [kt.gpr], by rw [kt.gpr], by rw [kt.gpr], kt.rd, kt.wr⟩
  refine ⟨ku.trans ((IKeep.of_field kv).trans (IKeep.of_mem keep kt.mem)),
    (congrFun kt.gpr .esi).trans bv, ?_, ?_, ?_⟩
  · show t.zf.map (!·) = _
    rw [zt, BitVec.and_self, bv, Wp.ofNat_beq_zero (by omega)]; rfl
  · rw [kt.mem]; exact vp
  · rw [kt.mem]; exact dv

end VG.Proof.Ed25519.X86
