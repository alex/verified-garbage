import VerifiedGarbage.Proof.X25519.Arm.Ladder
import VerifiedGarbage.Proof.X25519.Invert

/-!
# X25519 on 32-bit ARM: the inversion

Untrusted: everything here is checked by Lean. `invert` computes
`z^(p-2)` into `R` for the element `z` at `Z2` by square-and-multiply over the
bits of `p - 2` from 254 down to 0 (`invert_ok`): after the bits down to `n`,
`R` holds `z^((p - 2) >> n)`.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)
open Fin.CommRing

/-! ## The bits of `p - 2` -/

def pbitsB : Nat → Bool
  | 0 => true
  | t + 1 => ((P - 2) >>> t % 2 == if t = 4 ∨ t = 2 then 0 else 1) && pbitsB t

theorem pbitsB_ok : pbitsB 255 = true := by decide +kernel

/-- Every bit of `p - 2 = 2²⁵⁵ - 21` but bits 4 and 2 (and those from 255 up) is 1. -/
theorem pbits : ∀ t < 255, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
  have : ∀ n, pbitsB n = true → ∀ t < n, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega
    | succ n ih =>
      intro h t ht
      simp only [pbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 255 pbitsB_ok

theorem p255 : (P - 2) >>> 255 = 0 := by decide +kernel

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem shr_step (x t : Nat) : x >>> t = 2 * (x >>> (t + 1)) + x >>> t % 2 := by
  rw [Nat.shiftRight_succ]; omega

/-! ## Stores of a register -/

section
variable {b : BitVec 32}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (v Z2 ^ ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : BitVec 32) (sI : State) (c : BitVec 32) (v : Nat → Fe) (n : Nat) (s : State) :
    Prop where
  cur : Cur b sI (BitVec.ofNat 32 n) c IQ (invV v n) s

theorem sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 32 x = BitVec.ofNat 32 y := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 x) (BitVec.ofNat 32 y), h']; simp
    have := congrArg BitVec.toNat e
    rwa [toNat_imm hx, toNat_imm hy] at this

theorem Cur.congr {s0 s : State} {a c : BitVec 32} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r10, h.r11, (h.slots.mono hq).congr hv⟩

theorem invStep_ok {sI : State} {c : BitVec 32} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI c v n s) :
    WP isa invStep s fun s' => InvInv b sI c v (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  obtain ⟨hcur⟩ := h
  have hb := pbits (n - 1) (by omega)
  have he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (wp_dp (op2_imm (by decide)) fun s1 u1 => WP.block_nil ?_)
  have h1 : Cur b sI (BitVec.ofNat 32 (n - 1)) c IQ (invV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide) u1.mem), ?_,
      by rw [u1.other _ (by decide), hcur.r11], by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr]; show s.gpr .r10 - 1 = _
    rw [hcur.r10]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
  refine WP.seq (WP.mono (opMul (o := R) (x := R) (y := R) (by decide) (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  -- After the square.
  have hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (v Z2 ^ (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, two_mul, pow_add]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := IQ) (by decide) hsq
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s3 u3 hz3 => WP.block_nil ?_)
  have h3 := h2'.next (Fupd.rest u3 _) (by rw [u3.mem]; exact Frame.refl _ _) (by rw [u3.mem]; exact h2'.slots)
  have hz3' : s3.z = decide (n - 1 = 4) := by
    rw [hz3, h2'.r10]; exact sub_beq (by omega) (by decide)
  refine WP.seq (WP.mono (Q := Cur b sI (BitVec.ofNat 32 (n - 1)) c IQ (invV v (n - 1))) ?_ fun s4 h4 =>
    wp_cmp (op2_imm (by decide)) fun s5 u5 hz5 => WP.block_nil ⟨⟨h4.next (Fupd.rest u5 _)
      (by rw [u5.mem]; exact Frame.refl _ _) (by rw [u5.mem]; exact h4.slots)⟩, ?_⟩)
  · refine WP.ite s3.z (eval_eq _) (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_))
      (fun hf => ?_)
    · have h4 : n - 1 = 4 := by rw [hz3'] at ht; simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h4 : n - 1 ≠ 4 := by rw [hz3'] at hf; simpa using hf
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s4 u4 hz4 => WP.block_nil ?_)
      have h4' := h3.next (Fupd.rest u4 _) (by rw [u4.mem]; exact Frame.refl _ _) (by rw [u4.mem]; exact h3.slots)
      have hz4' : s4.z = decide (n - 1 = 2) := by
        rw [hz4, h3.r10]; exact sub_beq (by omega) (by decide)
      refine WP.ite s4.z (eval_eq _) (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) fun q _ => ?_))
        (fun hf => ?_)
      · have h2 : n - 1 = 2 := by rw [hz4'] at ht; simpa using ht
        by_cases hq : q = R
        · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
        · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
      · have h2 : n - 1 ≠ 2 := by rw [hz4'] at hf; simpa using hf
        refine WP.mono (opMul (o := R) (x := R) (y := Z2) (by decide) (by decide) (by decide) (by decide) h4')
          fun s5 h5 => h5.congr (by decide) fun q _ => ?_
        by_cases hq : q = R
        · subst hq
          rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
            iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega), pow_add, pow_one]
        · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · rw [hz5, h4.r10]; exact sub_beq (by omega) (by decide)

theorem invert_ok {c : BitVec 32} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem (State.addr b) [Z2, X2] v) (h11 : s.gpr .r11 = c) :
    WP isa Impl.X25519.Arm.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem (State.addr b) IQ (upd v R (v Z2 ^ (P - 2))) := by
  unfold Impl.X25519.Arm.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r2] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine str0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 15) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r1, .r2, .r10] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 16, limb s5.mem (State.addr b) R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega)
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega, u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega, ite_false]; rfl
  have hf5 : Frame [⟨State.addr b + BitVec.ofNat 64 R, 64⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s2.gpr .r1)
      (Offset.contains (State.addr b) (d := R) (n := 4) (e := R) (k := 64) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩⟩
  have hS5 : SlotsOk s5.mem (State.addr b) IQ (invV v 255) := by
    have hZ2 : Z2 = 192 := rfl
    have hX2 : X2 = 128 := rfl
    have hR : R = 1024 := rfl
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e := limb_frame (o := Z2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS Z2 (by decide)).1 k hk, ?_⟩
      rw [FS, V, val16_congr e, invV, upd_of_ne _ _ (by decide)]; exact (hS Z2 (by decide)).2
    · refine ⟨fun k hk => by rw [hlimb k hk]; split <;> decide, ?_⟩
      rw [FS, V, val16_congr hlimb, invV, upd_self, p255, pow_zero]
      rfl
    · have e := limb_frame (o := X2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS X2 (by decide)).1 k hk, ?_⟩
      rw [FS, V, val16_congr e, invV, upd_of_ne _ _ (by decide)]; exact (hS X2 (by decide)).2
  have h255 : InvInv b s5 c v 255 s5 :=
    ⟨⟨hc5, Stp.refl _ _, u5.gpr, by rw [hr5.gpr _ (by decide), h11], hS5⟩⟩
  refine WP.mono (Q := InvInv b s5 c v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s5 c v m s') ?_ 255 s5 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega, by omega, by omega, hl'⟩

end

end VG.Proof.X25519.Arm
