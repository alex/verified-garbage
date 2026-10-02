import VerifiedGarbage.Proof.Ed25519.Arm.PointAccumulate

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
  frame : Frame [FA ACC b] s.mem t.mem

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
