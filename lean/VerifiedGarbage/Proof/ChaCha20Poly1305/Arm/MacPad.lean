import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Prologue

/-!
# ChaCha20-Poly1305 on ARMv7: absorbing padded data

Untrusted: everything here is checked by Lean. `macPad p n` absorbs the `n`
bytes at `p` into the Poly1305 state (at `ctx`), and zeros to a multiple of
16: `msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and wp_subs wp_cmp wp_ldr wp_str
  wp_ldrb wp_strb op2_imm op2_reg op2_lsr eval_eq eval_ne ofNat_beq_zero sub_ofNat ofNat_shr)
open VG.Proof.ChaCha20.Arm.Xor (writeW8_apply)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-- The Poly1305 state and the padded block. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 0 128, sub s₀ padOff 16]

theorem kept_mac {s₀ s s' : State} {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h : (k = 0 ∧ n = 128) ∨ (k = padOff ∧ n = 16)) : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by simp, fun _ h => h⟩

theorem kept_mac0 {s₀ s s' : State} (hk : Kept [] s s') : Kept (macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem mac_inv {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept (macR s₀) s s') : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_inv s₀ (by simp [padOff]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_disj s₀ (by simp [savOff, padOff]) (by simp [savOff])
        (by simp [padOff]))

/-! ## Absorbing whole blocks -/

/-- `n` blocks at `p` absorbed, from `r1 = p` and `r2 = n`. -/
theorem absorb_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {p : BitVec 32} {n : Nat}
    (h1 : s.gpr .r1 = p) (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (hn : 16 * n < 2 ^ 32)
    (hdj : (sub s₀ 0 128).Disjoint ⟨State.addr p, 16 * n⟩) (hfit : p.toNat + 16 * n ≤ 2 ^ 32)
    (hc : Covers [⟨State.addr p, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa absorb s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128] s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ bytesAt s.mem (State.addr p) (16 * n)) := by
  unfold absorb
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Kept [] s s₁ := ⟨fun r hr _ => u₁.other r (by rintro rfl; simp [preserved] at hr), u₁.sp,
    u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  have i₁ := h.step0 k₁
  refine WP.seq (blocks_call (P := cP s₀) (p := p) (n := n) (by rw [u₁.gpr, hr7 h])
    (by rw [u₁.other _ (by decide), h1]) (by rw [u₁.other _ (by decide), h2]) hn
    (by rw [← sub_zero]; exact hdj) (by have := hp.fit_c; simp only [cP] at this ⊢; omega) hfit (fun a w hi => ?_)
    (by rw [← sub_zero]; exact covers1 hp i₁.wr (a := 0) (n := 128) (by omega)) fun s₂ k₂ r0₂ repr₂ => ?_)
  · obtain ⟨r, hr, hcn⟩ := hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [i₁.rd, i₁.wr]; exact hc a w ⟨_, List.mem_singleton_self _, hcn⟩
    · rw [← sub_zero] at hcn
      exact covers_left _ (covers1 hp i₁.wr (a := 0) (n := 128) (by omega)) a w ⟨_, List.mem_singleton_self _, hcn⟩
  rw [← sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by omega) (by simp [savOff])
  refine WP.mono (anchor_ok i₂ r0₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans
    (k₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil)), fun key msg hr => ?_⟩
  rw [k₃.mem_eq, ← k₁.mem_eq]
  exact repr₂ key msg (by rw [k₁.mem_eq]; exact hr)

/-! ## Zeroing the padded block -/

theorem writeW32_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rfl

theorem padZ_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.mov .r12 (.imm 0), .str .r12 .r7 padOff, .str .r12 .r7 (padOff + 4),
      .str .r12 .r7 (padOff + 8), .str .r12 .r7 (padOff + 12),
      .dp .add .r2 .r7 (.imm (BitVec.ofNat 32 padOff))]) s fun s' =>
      s'.gpr .r2 = ptr s₀ padOff ∧ (∀ r, r ≠ .r12 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ padOff 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (padOff + j)) = 0 := by
  have o : ∀ d, d < 4 → InRegions s.wr (off (cx s₀) (padOff + 4 * d)) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx (by simp [padOff]; omega)
  have ea : ∀ d, d < 4 → State.addr (cP s₀ + BitVec.ofNat 32 (padOff + 4 * d)) = off (cx s₀) (padOff + 4 * d) :=
    fun d hd => hp.addr_cP_off (by simp [padOff]; omega)
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have h7 : s₁.gpr .r7 = cP s₀ := by rw [u₁.other _ (by decide), hr7 h]
  refine wp_str (a := off (cx s₀) (padOff + 4 * 0)) (by simp [padOff]) (by rw [h7]; exact ea 0 (by omega))
    (by rw [u₁.wr]; exact o 0 (by omega)) fun s₂ g₂ => ?_
  refine wp_str (a := off (cx s₀) (padOff + 4 * 1)) (by simp [padOff]) (by rw [g₂.gpr, h7]; exact ea 1 (by omega))
    (by rw [g₂.wr, u₁.wr]; exact o 1 (by omega)) fun s₃ g₃ => ?_
  refine wp_str (a := off (cx s₀) (padOff + 4 * 2)) (by simp [padOff])
    (by rw [g₃.gpr, g₂.gpr, h7]; exact ea 2 (by omega))
    (by rw [g₃.wr, g₂.wr, u₁.wr]; exact o 2 (by omega)) fun s₄ g₄ => ?_
  refine wp_str (a := off (cx s₀) (padOff + 4 * 3)) (by simp [padOff])
    (by rw [g₄.gpr, g₃.gpr, g₂.gpr, h7]; exact ea 3 (by omega))
    (by rw [g₄.wr, g₃.wr, g₂.wr, u₁.wr]; exact o 3 (by omega)) fun s₅ g₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have x12 : s₁.gpr .r12 = 0 := u₁.gpr
  have hm : s₆.mem = (((s.mem.writeW (off (cx s₀) (padOff + 4 * 0)) (0 : BitVec 32)).writeW
      (off (cx s₀) (padOff + 4 * 1)) (0 : BitVec 32)).writeW (off (cx s₀) (padOff + 4 * 2)) (0 : BitVec 32)).writeW
      (off (cx s₀) (padOff + 4 * 3)) (0 : BitVec 32) := by
    rw [u₆.mem, g₅.mem, g₄.gpr, g₄.mem, g₃.gpr, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x12]
  refine ⟨by rw [u₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, h7], fun r h₁ h₂ => by
      rw [u₆.other _ h₂, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, u₁.wr],
    by rw [u₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, u₁.sp], ?_, fun j hj => ?_⟩
  · rw [hm]
    have c : ∀ d, d < 4 → (sub s₀ padOff 16).Contains (off (cx s₀) (padOff + 4 * d)) (32 / 8) :=
      fun d hd => contains_sub s₀ (by omega) (by omega) (by simp [padOff])
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 1 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 2 (by omega))
      |>.writeW (List.mem_singleton_self _) _ (c 3 (by omega))
  · rw [hm]
    have e : ∀ d, d ≤ j → (off (cx s₀) (padOff + j) - off (cx s₀) (padOff + d)).toNat = j - d := by
      intro d hd
      rw [show off (cx s₀) (padOff + j) - off (cx s₀) (padOff + d) = BitVec.ofNat 64 (j - d) by
          show cx s₀ + BitVec.ofNat 64 (padOff + j) - (cx s₀ + BitVec.ofNat 64 (padOff + d)) = _
          rw [show padOff + j = (padOff + d) + (j - d) by omega, BitVec.ofNat_add]; bv_omega,
        toNat_ofNat_lt (by omega)]
    have e' : ∀ d, j < d → d < 16 → ¬ (off (cx s₀) (padOff + j) - off (cx s₀) (padOff + d)).toNat < 4 := by
      intro d hd hd'
      rw [show off (cx s₀) (padOff + j) - off (cx s₀) (padOff + d) = BitVec.ofNat 64 (2 ^ 64 - (d - j)) by
          show cx s₀ + BitVec.ofNat 64 (padOff + j) - (cx s₀ + BitVec.ofNat 64 (padOff + d)) = _
          simp only [padOff]; bv_omega, toNat_ofNat_lt (by omega)]
      omega
    simp only [writeW32_zero_apply]
    rcases (by omega : j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j) with hj' | hj' | hj' | hj'
    · simp (disch := omega) only [e' (4 * 3), e' (4 * 2), e' (4 * 1), ite_false, e (4 * 0),
        Nat.mul_zero, Nat.sub_zero, hj', ite_true]
    · simp (disch := omega) only [e' (4 * 3), e' (4 * 2), ite_false, e (4 * 1), show j - 4 * 1 < 4 by omega,
        ite_true]
    · simp (disch := omega) only [e' (4 * 3), ite_false, e (4 * 2), show j - 4 * 2 < 4 by omega, ite_true]
    · simp (disch := omega) only [e (4 * 3), show j - 4 * 3 < 4 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : BitVec 32) (t i : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = Q + BitVec.ofNat 32 i
  r2 : s.gpr .r2 = ptr s₀ (padOff + i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ padOff 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (padOff + j)) =
    if j < i then s₂.mem (State.addr Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.ldrb .r12 .r1 0, .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1), .dp .add .r2 .r2 (.imm 1),
   .subs .r3 .r3 (.imm 1)]

theorem copyLoop_eq : copyLoop = .loop (.block copyBody) .ne := rfl

theorem byte_rt (b : Byte) : ((b.setWidth 32).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem off_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) : off p a ≠ off p b := by
  intro he
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have e := congrArg (· - p) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  exact h this

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} {Q : BitVec 32} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr) (hQ : Q.toNat + t ≤ 2 ^ 32)
    (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (State.addr Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨State.addr Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16))
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s fun s' => CpInv s₀ s₂ Q t (i + 1) s' ∧ s'.z = (BitVec.ofNat 32 (t - (i + 1)) == 0) := by
  have hin : InRegions (s.rd ++ s.wr) (State.addr Q + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (padOff + i)) 1 := by
    rw [h.wr, hwr]; exact hp.in_ctx (by simp [padOff]; omega)
  unfold copyBody
  refine wp_ldrb (a := State.addr Q + BitVec.ofNat 64 i) (by decide)
    (by rw [h.r1, show Q + BitVec.ofNat 32 i + BitVec.ofNat 32 0 = Q + BitVec.ofNat 32 i from BitVec.add_zero _]
        exact addr_add (a := Q) (k := i) (by omega)) hin fun s₁ u₁ => ?_
  refine wp_strb (a := off (cx s₀) (padOff + i)) (by decide)
    (by rw [u₁.other _ (by decide), h.r2,
          show ptr s₀ (padOff + i) + BitVec.ofNat 32 0 = ptr s₀ (padOff + i) from BitVec.add_zero _]
        exact hp.addr_ptr (by simp [padOff]; omega))
    (by rw [u₁.wr]; exact hout) fun s₂' g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have r3₄ : s₄.gpr .r3 = BitVec.ofNat 32 (t - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r3]
  have e3 : s₄.gpr .r3 - 1 = BitVec.ofNat 32 (t - (i + 1)) := by
    rw [r3₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hm : s₅.mem = s.mem.writeW (off (cx s₀) (padOff + i)) (s.mem (State.addr Q + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, byte_rt]
  have hg : ∀ r ∈ preserved, s₅.gpr r = s.gpr r := fun r hr => by
    have h1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    have h2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, g₂.gpr, u₁.other _ h12]
  refine ⟨⟨?_, ?_, ?_, fun r hr => by rw [hg r hr, h.keep r hr], ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat32]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ptr, add_ofNat32, Nat.add_assoc]
  · rw [u₅.gpr, e3]
  · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
  · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (w := 8 / 8) (by omega) (by omega)
      (by simp [padOff]))
  · have hbyte : s.mem (State.addr Q + BitVec.ofNat 64 i) = s₂.mem (State.addr Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdisj i hi _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, hbyte]
    · simp only [off_ne (cx s₀) (a := padOff + k) (b := padOff + i) (by simp [padOff]; omega)
        (by simp [padOff]; omega) (by omega), ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [z₅, e3]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (padOff + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) padOff) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) padOff + BitVec.ofNat 64 k = off (cx s₀) (padOff + k) from off_off _ _ _, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padTail_eq : padTail =
    .seq (.block [.mov .r12 (.imm 0), .str .r12 .r7 padOff, .str .r12 .r7 (padOff + 4),
      .str .r12 .r7 (padOff + 8), .str .r12 .r7 (padOff + 12),
      .dp .add .r2 .r7 (.imm (BitVec.ofNat 32 padOff))])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) absorb)) := rfl

theorem ptA_ok {s₀ : State} {s : State} (h : Inv s₀ s) :
    WP isa (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = ptr s₀ padOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ Kept [] s s' := by
  have core : WP isa (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) s
      fun s' => s'.gpr .r1 = ptr s₀ padOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_add (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, hr7 h], by rw [u₂.gpr]; rfl,
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem padTail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {Q : BitVec 32} {t : Nat}
    (ht0 : 0 < t) (ht : t < 16) (h1 : s.gpr .r1 = Q) (h3 : s.gpr .r3 = BitVec.ofNat 32 t)
    (hQ : Q.toNat + t ≤ 2 ^ 32)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (State.addr Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨State.addr Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ padOff 16)) :
    WP isa padTail s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem (State.addr Q) t ++ List.replicate (16 - t) 0)) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono (padZ_ok hp h) fun s₂ ⟨r2₂, g₂, rd₂, wr₂, sp₂, f₂, z₂⟩ => ?_)
  have src₂ : ∀ j < t, s₂.mem (State.addr Q + BitVec.ofNat 64 j) = s.mem (State.addr Q + BitVec.ofNat 64 j) :=
    fun j hj => f₂ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj j hj _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  have hk₂ : Kept [sub s₀ padOff 16] s s₂ :=
    ⟨fun r hr _ => g₂ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      sp₂, rd₂, wr₂, f₂⟩
  have i₂ := h.step1 hk₂ (by simp [padOff]) (by simp [padOff, savOff])
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · let I : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, I n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval .ne s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval .ne s' = some true ∧ ∃ n' < n, I n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [i₂.wr]) hQ (by rw [rd₂, wr₂]; exact hsrc) hdisj hi hI)
        fun s' ⟨h', hz⟩ => ?_
      have hz' : isa.eval .ne s' = some (decide (t - (i + 1) ≠ 0)) := by
        show some (!s'.z) = _
        rw [hz, ofNat_beq_zero (by omega)]; simp
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz']; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz']; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) I hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), h1]; simp,
      by rw [r2₂]; rfl, by rw [g₂ _ (by decide) (by decide), h3]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have hk₃ : Kept [sub s₀ padOff 16] s₂ s₃ := ⟨fun r hr _ => h₃.keep r hr, h₃.sp, h₃.rd, h₃.wr, h₃.frame⟩
  have i₃ := i₂.step1 hk₃ (by simp [padOff]) (by simp [padOff, savOff])
  refine WP.seq (WP.mono (ptA_ok i₃) fun s₄ ⟨h1₄, h2₄, k₄⟩ => ?_)
  have i₄ := i₃.step0 k₄
  refine WP.mono (absorb_ok hp i₄ (n := 1) h1₄ h2₄ (by omega)
    (by rw [hp.addr_ptr (by simp [padOff])]
        exact sub_disj s₀ (a := 0) (n := 128) (by simp [padOff]) (by omega) (by simp [padOff]))
    (by rw [hp.ptr_toNat (by simp [padOff])]; have := hp.fit_c; simp [padOff]; omega)
    (by rw [hp.addr_ptr (by simp [padOff])]
        exact covers_left _ (covers1 hp rfl (a := padOff) (n := 16 * 1) (by simp [padOff]))))
    fun s₅ ⟨i₅, k₅, repr₅⟩ => ⟨i₅, (kept_mac hk₂ (.inr ⟨rfl, rfl⟩)).trans ((kept_mac hk₃ (.inr ⟨rfl, rfl⟩)).trans
      ((kept_mac0 k₄).trans (kept_mac k₅ (.inl ⟨rfl, rfl⟩)))), fun key msg hr => ?_⟩
  have m₄ := k₄.mem_eq
  have hr₄ : Repr s₄.mem (cx s₀) key msg := by
    rw [m₄]
    refine Repr.frame (f₂.trans h₃.frame) (fun r hr => ?_) hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero]; exact sub_disj s₀ (by simp [padOff]) (by omega) (by simp [padOff])
  have hb : bytesAt s₄.mem (State.addr (ptr s₀ padOff)) (16 * 1) =
      bytesAt s.mem (State.addr Q) t ++ List.replicate (16 - t) 0 := by
    rw [m₄, hp.addr_ptr (by simp [padOff]), show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
    refine congrArg (· ++ _) (bytesAt_eq_of fun j hj => src₂ j hj)
  have := repr₅ key msg hr₄
  rwa [hb] at this

/-! ## The whole of `macPad` -/

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .r8 ∨ p = .r10) ∧ (n = .r9 ∨ n = .r11)

theorem MacRegs.p_ne {p n : Reg} (hr : MacRegs p n) :
    p ≠ .r0 ∧ p ≠ .r1 ∧ p ≠ .r2 ∧ p ≠ .r3 ∧ p ≠ .r12 ∧ p ∈ preserved ∧ p ≠ .lr := by
  rcases hr.1 with rfl | rfl <;> decide

theorem MacRegs.n_ne {p n : Reg} (hr : MacRegs p n) :
    n ≠ .r0 ∧ n ≠ .r1 ∧ n ≠ .r2 ∧ n ≠ .r3 ∧ n ≠ .r12 ∧ n ∈ preserved ∧ n ≠ .lr := by
  rcases hr.2 with rfl | rfl <;> decide

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  lt : len < 2 ^ 32
  fit : P.toNat + len ≤ 2 ^ 32
  ctx : (ctxR s₀).Disjoint ⟨State.addr P, len⟩
  cov : Covers [⟨State.addr P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x 1) : (⟨P, len⟩ : Region).Contains x 1 :=
  sub_off P h x hc

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)]) s fun s' =>
      s'.gpr .r1 = s.gpr p ∧ s'.gpr .r2 = s.gpr n >>> 4 ∧ Kept [] s s' := by
  have hp := hr.p_ne
  have hn := hr.n_ne
  have core : WP isa (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)]) s fun s' =>
      s'.gpr .r1 = s.gpr p ∧ s'.gpr .r2 = s.gpr n >>> 4 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ hn.2.1],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem macC_ok (n : Reg) (s : State) :
    WP isa (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 ((s.gpr n).toNat % 16) ∧
      s'.z = (BitVec.ofNat 32 ((s.gpr n).toNat % 16) - 0 == 0) ∧ Kept [] s s' := by
  have core : WP isa (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 ((s.gpr n).toNat % 16) ∧
      s'.z = (BitVec.ofNat 32 ((s.gpr n).toNat % 16) - 0 == 0) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem :=
    wp_and (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ u₂ z₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.gpr, and15], by rw [z₂, u₁.gpr, and15], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
        by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h3, hz, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h3, hz, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) s fun s' =>
      s'.gpr .r1 = s.gpr p + (s.gpr n - s.gpr .r3) ∧ (∀ r, r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      Kept [] s s' := by
  have hp := hr.p_ne
  have core : WP isa (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) s fun s' =>
      s'.gpr .r1 = s.gpr p + (s.gpr n - s.gpr .r3) ∧ (∀ r, r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_sub (op2_reg _ _) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.other _ hp.2.1, u₁.gpr], fun r h => by rw [u₂.other _ h, u₁.other _ h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, hg', hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, hg', Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macPad_eq (p n : Reg) : macPad p n =
    .seq (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)])
    (.seq absorb
    (.seq (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)])
      (.ite .eq (.block [])
        (.seq (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) padTail)))) := rfl

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {p n : Reg} (hr : MacRegs p n) {P : BitVec 32} {len : Nat}
    (hs : Src s₀ P len) {s : State} (h : Inv s₀ s) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 32 len) :
    WP isa (macPad p n) s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (bytesAt s.mem (State.addr P) len ++
          pad16 (bytesAt s.mem (State.addr P) len))) := by
  have hpn := hr.p_ne
  have hnn := hr.n_ne
  have hlt := hs.lt
  have hcP : (ctxR s₀).Disjoint ⟨State.addr P, len⟩ := hs.ctx
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  rw [macPad_eq]
  refine WP.seq (WP.mono (macA_ok hr s) fun s₁ ⟨r1₁, r2₁, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  refine WP.seq (WP.mono (absorb_ok hp i₁ (p := P) (n := len / 16) (by rw [r1₁, hP])
    (by rw [r2₁, hn, ofNat_shr hlt]) (by omega)
    ((hcP.sub_left (sub_ctx s₀ (by omega))).sub_right (Region.sub_prefix hk)) (by have := hs.fit; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ?_)
  have m₁ := k₁.mem_eq
  rw [m₁] at repr₂
  refine WP.seq (WP.mono (macC_ok n s₂) fun s₃ ⟨r3₃, z₃, k₃⟩ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 32 len := by
    rw [k₂.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, k₁.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, hn]
  have p₂ : s₂.gpr p = P := by
    rw [k₂.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, k₁.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, hP]
  rw [n₂, toNat32 hlt] at r3₃ z₃
  have i₃ := i₂.step0 k₃
  have k₁₃ : Kept (macR s₀) s s₃ :=
    (kept_mac0 k₁).trans ((kept_mac k₂ (.inl ⟨rfl, rfl⟩)).trans (kept_mac0 k₃))
  have x_eq : bytesAt s.mem (State.addr P) len = bytesAt s.mem (State.addr P) (16 * (len / 16)) ++
      bytesAt s.mem (State.addr P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem (State.addr P) len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₃ := k₃.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      show some s₃.z = _
      rw [z₃, show BitVec.ofNat 32 (len % 16) - 0 = BitVec.ofNat 32 (len % 16) from BitVec.sub_zero _,
        ofNat_beq_zero (by omega)]) (fun hb => ?_) (fun hb => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using hb
    refine WP.block_nil ⟨i₃, k₁₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem (State.addr P) len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using hb
    refine WP.seq (WP.mono (macD_ok hr s₃) fun s₄ ⟨r1₄, g₄, k₄⟩ => ?_)
    have i₄ := i₃.step0 k₄
    have hQ : s₄.gpr .r1 = P + BitVec.ofNat 32 (16 * (len / 16)) := by
      rw [r1₄, r3₃, k₃.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, n₂, k₃.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, p₂,
        sub_ofNat (by omega), show len - len % 16 = 16 * (len / 16) by omega]
    have hfitQ : (P + BitVec.ofNat 32 (16 * (len / 16))).toNat + len % 16 ≤ 2 ^ 32 := by
      have := hs.fit
      rw [BitVec.toNat_add, toNat32 (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have eQ : State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) = State.addr P + BitVec.ofNat 64 (16 * (len / 16)) :=
      addr_add (by have := hs.fit; omega)
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [i₄.rd, i₄.wr, eQ, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov _ _ ⟨_, List.mem_singleton_self _, contains_off_sub (a := 16 * (len / 16) + j) (n := 1)
        (by omega) (self_contains _)⟩
    have hdj : ∀ j < len % 16, (⟨State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ padOff 16) := fun j hj => by
      rw [eQ, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hcP.sub_left (sub_ctx s₀ (by simp [padOff]))).sub_right
        (sub_off (State.addr P) (a := 16 * (len / 16) + j) (n := 1) (by omega))).symm
    refine WP.mono (padTail_ok hp i₄ (Q := P + BitVec.ofNat 32 (16 * (len / 16))) (t := len % 16)
      (by omega) (by omega) hQ (by rw [g₄ _ (by decide), r3₃]) hfitQ hsrc hdj) fun s₅ ⟨i₅, k₅, repr₅⟩ => ?_
    refine ⟨i₅, k₁₃.trans ((kept_mac0 k₄).trans k₅), fun key msg hr => ?_⟩
    have m₄ := k₄.mem_eq
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, bytesAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [eQ]
        exact ((hcP.sub_left (sub_ctx s₀ (by omega))).sub_right
          (sub_off (State.addr P) (a := 16 * (len / 16)) (by omega))).symm) (by omega), m₁, eQ] at this
    rw [show pad16 (bytesAt s.mem (State.addr P) len) = List.replicate (16 - len % 16) 0 by
      simp [pad16, hlen, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.Arm
