import VerifiedGarbage.Impl.Ed25519.Arm.PointLoop
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Impl.Ed25519.Arm.PointPowers
import VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad

/-! Merged from `Proof.Ed25519.Arm.PointTableAddr`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PointLoop`. -/
section
/-! Fixed batches of exact doublings preserve the saved accumulator. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem doubleBody_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (n : Nat) (hn : n < 16) (hcount : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa doubleBody s fun t => t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      AllLim t.mem b ∧ point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hi⟩ => ?_)
  refine WP.mono (decR10_ok (by omega) ((hk.rest.gpr _ (by decide)).trans hcount))
    fun u ⟨hu, hz, hr, hm⟩ => ?_
  exact ⟨hu, hz, hm ▸ hlt, by rw [hm]; exact hv, by rw [hm]; exact hi,
    (IKeep.of_keep hk).trans (IKeep.of_counter hr hm)⟩

structure DoubleInv (s₀ : State) (b : BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  value : point (env s.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : IKeep b s₀ s

theorem doubleLoop_ok {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (hcount : s₀.gpr .r10 = 16) (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop doubleBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧ IKeep b s₀ t := by
  apply WP.loop (DoubleInv s₀ b) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (doubleBody_ok hi.ctx hi.lim k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htl, htv, hthi, htk⟩ => ?_
    have hv : point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, decide_true, Bool.not_true], htl, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hc, hl, hcount, rfl, fun _ _ => rfl,
      ⟨Rest.refl _ _, Frame.refl _ _⟩⟩

theorem double16_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hk : IKeep b s t := IKeep.of_counter (ht.rest (by decide)) ht.mem
  refine WP.mono (doubleLoop_ok (hk.ctx hc) (by rw [ht.mem]; exact hl)
    ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, hv, hh, hu⟩ => ?_
  rw [ht.mem] at hv hh
  exact ⟨hlu, hv, hh, hk.trans hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Public table addresses and bounded counters. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem movw_nat {v : Nat} (hv : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

theorem tableAddr_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (start j : Nat)
    (ho : start + 128 * j < 8192) (hj : j < 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr start)) s fun t =>
      t.gpr .r12 = b + BitVec.ofNat 32 (start + 128 * j) ∧
      Rest [.r3, .r12] s t ∧ t.mem = s.mem := by
  have hb := hc.fit
  refine wp_movw fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = start := by rw [u1.gpr, movw_nat (by omega)]
  have e2 : (s2.gpr .r12).toNat = b.toNat + start := by
    rw [u2.gpr]
    change (s1.gpr .r0 + s1.gpr .r3).toNat = _
    rw [u1.other _ (by decide), hc.r0, toNat_add_lt (by rw [e1]; omega), e1]
  have e11 : (s2.gpr .r11 <<< 7).toNat = 128 * j := by
    rw [u2.other _ (by decide), u1.other _ (by decide), h11, toNat_shl, toNat_imm (by omega)]
    omega
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  apply BitVec.eq_of_toNat_eq
  rw [u3.gpr]
  change (s2.gpr .r12 + (s2.gpr .r11 <<< 7)).toNat = _
  rw [toNat_add_lt (by rw [e2, e11]; omega), e2, e11, hc.ptr_nat ho]
  omega

theorem sub_beq_zero_nat {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 32) + BitVec.ofNat 32 y = BitVec.ofNat 32 y := BitVec.zero_add _
  rw [hz]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [toNat_imm hx, toNat_imm hy] at this
  · exact congrArg (BitVec.ofNat 32)

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 32)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧ t.z = decide (j + 1 = count) ∧
      Rest [.r3, .r11] s t ∧ t.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_cmp (op2_reg _ _) fun s3 u3 hz => WP.block_nil ?_
  have e2 : s2.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [u2.gpr]
    change s1.gpr .r11 + 1 = _
    rw [u1.other _ (by decide), h11, BitVec.ofNat_add]
    rfl
  have e3 : s2.gpr .r3 = BitVec.ofNat 32 count := by
    rw [u2.other _ (by decide), u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [movw_nat (by omega), toNat_imm (by omega)]
  exact ⟨by rw [u3.gpr]; exact e2,
    by rw [hz, e2, e3, sub_beq_zero_nat (by omega) (by omega)],
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest _)),
    by rw [u3.mem, u2.mem, u1.mem]⟩

end VG.Proof.Ed25519.Arm
end

/-! Constructing bounded tables of exact point doublings. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev TableFrame (b : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [FA b, ⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m'

theorem TableFrame.mono {b : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableFrame b o' n' m m' := by
  refine h.sub fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ ho hn⟩

theorem TableFrame.workspace {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [FA b] m m') : TableFrame b o n m m' :=
  h.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

theorem TableFrame.table {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') : TableFrame b o n m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem tablePoint_frame {b : BitVec 32} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, (⟨State.addr b + BitVec.ofNat 64 d, 128⟩ : Region).Disjoint r) :
    tablePoint m' b d = tablePoint m b d := by
  have he : ∀ i, i + 32 ≤ 128 → tableF m' b (d + i) = tableF m b (d + i) := by
    intro i hi
    refine congrArg VG.Proof.X25519.toFe (packedV_frame hf fun r hm => ?_)
    exact (hd r hm).sub_left (Offset.sub _ (by omega) (by omega))
  have h0 := he 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [tablePoint, h0, he 32 (by decide), he 64 (by decide), he 96 (by decide)]

theorem TableFrame.point {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') {d : Nat} (hd : 1600 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 ≤ 8192) (hn : o + n ≤ 8192) :
    tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint _ hsep (by omega) (by omega)

theorem workspace_tablePoint {b : BitVec 32} {m m' : Mem} (h : Frame [FA b] m m')
    {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

abbrev powersClob : List Reg := [.r10, .r11, .r12] ++ clob

structure PowersKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : TableFrame b o n s.mem t.mem

theorem PowersKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : PowersKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem PowersKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem PowersKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : PowersKeep b o n s t) (k : PowersKeep b o n t u) : PowersKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem PowersKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : PowersKeep b o' n' s t :=
  ⟨h.rest, TableFrame.mono h.frame ho hn⟩

theorem powerBatch_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  cases batch with
  | true => exact double16_ok hc hl hd
  | false =>
    refine WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hh⟩ => ?_
    exact ⟨hlt, hv, hh, IKeep.of_keep hk⟩

theorem powersBody_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) (o j count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (powersBody o count batch) s fun t => t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧
      t.z = decide (j + 1 = count) ∧ AllLim t.mem b ∧
      tablePoint t.mem b (o + 128 * j) = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧
      PowersKeep b (o + 128 * j) 128 s t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hc o j (by omega) (by omega) h11) fun t ⟨htp, htr, htm⟩ => ?_
  have hct := hc.of_rest htr (by decide)
  refine WP.mono (pointToTable_ok hct (by rw [htm]; exact hl) htp (by omega) (by omega))
    fun u ⟨hut, huk⟩ => ?_
  have heu : env u.mem b = env s.mem b := (huk.env (by omega) (by omega)).trans
    (congrArg (fun m => env m b) htm)
  refine WP.seq (WP.mono (powerBatch_ok (huk.ctx hct)
    (huk.lim (by omega) (by omega) (by rw [htm]; exact hl)) (by rw [heu]; exact hd) batch)
    fun v ⟨hvl, hvp, hvhi, hvk⟩ => ?_)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hvk.rest.gpr _ (by decide), huk.rest.gpr _ (by decide), htr.gpr _ (by decide), h11]
  refine WP.mono (powersNext_ok v j count hj hn hvc) fun w ⟨hwc, hwz, hwr, hwm⟩ => ?_
  refine ⟨hwc, hwz, by rw [hwm]; exact hvl, ?_, ?_, ?_, ?_⟩
  · rw [hwm, workspace_tablePoint hvk.frame (by omega) (by omega), hut, htm]
  · rw [hwm, hvp, heu]
  · intro i hi
    rw [hwm, hvhi i hi, heu]
  · refine ⟨(htr.mono (by decide)).trans ((huk.rest.mono (by decide)).trans
      ((hvk.rest.mono (by decide)).trans (hwr.mono (by decide)))), ?_⟩
    rw [hwm, ← htm]
    exact (TableFrame.table huk.frame).trans (TableFrame.workspace hvk.frame)

end VG.Proof.Ed25519.Arm
