import VerifiedGarbage.Proof.Ed25519.X86.Workspace
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.Scalar

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

theorem scalarK_num : num (fun k => (scalarK k).toNat) 8 = 2 ^ 256 - L := by decide

theorem scalarDouble_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : acc s < 2) :
    WP isa (.block scalarDouble) s fun t => Keep s t ∧ Frame [sub x scalarR 32] s.mem t.mem ∧
      fe t.mem x scalarR = 2 * fe s.mem x scalarR + acc s := by
  have hs : num (fun k => colv s.mem x [.mulI (scalarR + 4 * k) 2]) 8 =
      2 * fe s.mem x scalarR := by
    rw [fe, ← num_mul]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    change wv s.mem x (scalarR + 4 * k) * 2 = 2 * wv s.mem x (scalarR + 4 * k)
    exact Nat.mul_comm _ _
  refine WP.mono (cols_ok hc _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by omega_using [hb])) fun t ⟨keep, frame, eq, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by simp only [scalarR]; omega_using [hk], Or.inr (Nat.le_refl _)⟩
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := wv_lt s.mem x (scalarR + 4 * k)
    change wv s.mem x (scalarR + 4 * k) * 2 < 2 ^ 68
    omega_using [hw]
  · rw [hs] at eq
    change fe t.mem x scalarR + 2 ^ 256 * acc t = _ at eq
    have hL := order_bound
    have hz : acc t = 0 := by omega_using [eq, hr, hb, hL]
    exact ⟨keep, frame, by rw [hz, Nat.mul_zero, Nat.add_zero] at eq; omega_using [eq]⟩

theorem scalarSubtract_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarSubtract) s fun t => Keep s t ∧ Frame [sub x T 32] s.mem t.mem ∧
      fe t.mem x T + 2 ^ 256 * acc t = fe s.mem x scalarR + (2 ^ 256 - L) := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  have hs : num (fun k => colv u.mem x [.addM (scalarR + 4 * k), .addI (scalarK k)]) 8 =
      fe s.mem x scalarR + (2 ^ 256 - L) := by
    rw [← scalarK_num, fe, ← num_add, mu]
    exact num_congr fun k _ => by
      simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  refine WP.mono (cols_ok (ku.ctx hc) _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [treads, List.mem_singleton] at hd; subst hd
      exact ⟨by simp only [scalarR]; omega_using [hk], Or.inl (by simp only [scalarR, T]; omega_using [hk])⟩
    · simp only [treads, List.not_mem_nil] at hd
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := wv_lt u.mem x (scalarR + 4 * k)
    have hk := (scalarK k).isLt
    omega_using [hw, hk]
  · rw [au, Nat.zero_add, hs] at et
    rw [mu] at ft
    exact ⟨ku.trans kt, ft, et⟩

/-- The carry is the comparison with L; the low limbs are the subtraction. -/
theorem scalar_subtract_value {r t c : Nat} (hr : r < 2 * L) (ht : t < 2 ^ 256)
    (h : t + 2 ^ 256 * c = r + (2 ^ 256 - L)) :
    c ≤ 1 ∧ (if c = 1 then t else r) = r % L := by
  have hl := order_bound
  have hp := order_pos
  constructor
  · omega_using [hr, ht, h, hl]
  · by_cases hc : c = 1
    · rw [ite_eq_left hc, Nat.mod_eq_sub_mod (by omega_using [h, hc, hp, hl]),
        Nat.mod_eq_of_lt (by omega_using [hr, h, hc, hl])]
      omega_using [h, hc, hl]
    · have hz : c = 0 := by omega_using [hr, h, hc, hl]
      rw [ite_eq_right hc, Nat.mod_eq_of_lt (by omega_using [ht, h, hz, hl])]

theorem scalarMask_ok {s : State} (ha : acc s ≤ 1) :
    WP isa (.block scalarMask) s fun t => Keep s t ∧ t.mem = s.mem ∧
      t.gpr .ecx = mask (acc s) := by
  refine Wp.wp_movi fun u hu => Wp.wp_sub fun t ht _ => WP.block_nil ?_
  refine ⟨(updKeep hu).trans (updKeep ht), ht.mem.trans hu.mem, ?_⟩
  rw [ht.gpr, hu.gpr, hu.other .ebx (by decide)]
  have hb : (s.gpr .ebx).toNat = acc s := by
    have he := (s.gpr .ebx).isLt
    change _ ≤ 1 at ha
    simp only [acc, v] at ha ⊢
    omega_using [ha, he]
  have hw : s.gpr .ebx = BitVec.ofNat 32 (acc s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hb, Nat.mod_eq_of_lt (by omega_using [ha])]
  rw [hw]; rfl

theorem scalarRound_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : acc s < 2) :
    WP isa (.block scalarRound) s fun t => Keep s t ∧
      Frame [sub x scalarR 32, sub x T 32] s.mem t.mem ∧
      fe t.mem x scalarR = (2 * fe s.mem x scalarR + acc s) % L := by
  simp only [scalarRound, List.append_assoc]
  refine WP.block_append (WP.mono (scalarDouble_ok hc hr hb) fun u ⟨ku, fu, eu⟩ => ?_)
  refine WP.block_append (WP.mono (scalarSubtract_ok (ku.ctx hc)) fun v ⟨kv, fv, ev⟩ => ?_)
  have hv := scalar_subtract_value (by rw [eu]; omega_using [hr, hb]) (fe_lt v.mem x T) ev
  refine WP.block_append (WP.mono (scalarMask_ok hv.1) fun w ⟨kw, mw, ew⟩ => ?_)
  have ewR : fe w.mem x scalarR = fe u.mem x scalarR := by
    rw [mw]; exact fe_frame1 fv hc.fit (by decide) (by decide) (Or.inl (by decide))
  refine WP.mono (selects_ok (kw.ctx (kv.ctx (ku.ctx hc))) (o := scalarR)
    (g := acc v) (by decide) hv.1 ew 8 (by decide) w
    ⟨Keep.refl _, rfl, Frame.refl _ _, fun _ h => by omega_using [h]⟩)
    fun t ht => ⟨ku.trans (kv.trans (kw.trans ht.keep)), ?_, ?_⟩
  · have fm : Frame [sub x scalarR 32, sub x T 32] u.mem w.mem := by
      rw [mw]; exact fv.mono fun r h => List.mem_cons_of_mem _ h
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]).trans
      (fm.trans (ht.frame.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]))
  · have es : fe t.mem x scalarR = if acc v = 1 then fe w.mem x T else fe w.mem x scalarR := by
      split
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_left ‹_›))
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_right ‹_›))
    rw [es, ewR, mw, hv.2, eu]

end VG.Proof.Ed25519.X86
