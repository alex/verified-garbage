import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Block

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: a block of the derived key to `out`, and the loop

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Proof.Sha256.AArch64 (contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.Sha256.AArch64.Stream (wp_ldrb wp_strb wp_addImm wp_subImm ofNat_succ ofNat_pred ofNat_beq_zero
  eval_zero eval_nonzero sub_ofNat)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_snoc writeBytes_nil)
open VG.Proof.Pbkdf2.X86_64.Derive (copy_frame bytesAt_succ' bytesAt_take)
open VG.AArch64.RegBlock (upd wp_run wp_run')

/-! ## Copying bytes -/

/-- `j` of the `n` bytes from `a` copied to `b`. -/
structure Cp (s : State) (a b : Addr) (n j : Nat) (s' : State) : Prop where
  x11 : s'.gpr .x11 = a + BitVec.ofNat 64 j
  x24 : s'.gpr .x24 = b + BitVec.ofNat 64 j
  x9 : s'.gpr .x9 = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x9 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : s'.mem = writeBytes s.mem b (bytesAt s.mem a j)

section
variable {s : State} {a b : Addr} {n : Nat} (hn : n < 2 ^ 64)
  (hin : ∀ i < n, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1)
  (hout : ∀ i < n, InRegions s.wr (b + BitVec.ofNat 64 i) 1)
  (hsep : Region.Disjoint ⟨a, n⟩ ⟨b, n⟩)
include hn hin hout hsep

theorem copy_step {j : Nat} (hj : j < n) {s' : State} (h : Cp s a b n j s') :
    WP isa (.block [.ldrb .x10 .x11 0, .strb .x10 .x24 0, .addImm .x .x11 .x11 1, .addImm .x .x24 .x24 1,
      .subImm .x .x9 .x9 1]) s' fun s'' =>
      Cp s a b n (j + 1) s'' ∧ s''.gpr .x9 = BitVec.ofNat 64 (n - (j + 1)) := by
  -- The byte read is not among those written.
  have hsrc : s'.mem (a + BitVec.ofNat 64 j) = s.mem (a + BitVec.ofNat 64 j) := by
    rw [h.mem]
    simp only [writeBytes, Proof.Hmac.X86_64.bytesAt_length]
    split
    · rename_i hc
      exfalso
      refine hsep (a + BitVec.ofNat 64 j) ?_ ?_
      · simp only [Region.Contains]
        rw [show a + BitVec.ofNat 64 j - a = BitVec.ofNat 64 j by bv_omega, toNat_ofNat_lt (by omega)]
        omega
      · simp only [Region.Contains]; omega
    · rfl
  refine wp_ldrb (a := a + BitVec.ofNat 64 j) (by decide) (by rw [h.x11]; simp)
    (by rw [h.rd, h.wr]; exact hin j hj) fun s₁ u₁ => ?_
  refine wp_strb (a := b + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other .x24 (by decide), h.x24]; simp)
    (by rw [u₁.wr, h.wr]; exact hout j hj) fun s₂ u₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hx9 : s₄.gpr .x9 = BitVec.ofNat 64 (n - j) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x9]
  have hx9' : s₅.gpr .x9 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, hx9, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨?_, ?_, hx9', fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩, hx9'⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.x11,
      add_ofNat]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x24,
      add_ofNat]
  · rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.gpr, u₁.other r h1, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₁.gpr, hsrc, h.mem, bytesAt_succ',
      writeBytes_snoc _ _ _ _ (by rw [Proof.Hmac.X86_64.bytesAt_length]; omega), Proof.Hmac.X86_64.bytesAt_length,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem copy_loop (hn0 : 0 < n) (h11 : s.gpr .x11 = a) (h24 : s.gpr .x24 = b)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 n) :
    WP isa byteLoop s (Cp s a b n n) := by
  have h₀ : Cp s a b n 0 s :=
    ⟨by rw [h11]; simp, by rw [h24]; simp, by rw [h9]; rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [show bytesAt s.mem a 0 = [] from rfl, writeBytes_nil]⟩
  refine WP.loop (M := isa) (fun m s' => ∃ j, m = n - j ∧ j < n ∧ Cp s a b n j s') ?_ n s ⟨0, rfl, hn0, h₀⟩
  rintro m s' ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hn hin hout hsep hj hc) fun s'' ⟨hc', hz⟩ => ?_
  have ev : isa.eval (.nonzero .x .x9) s'' = some (!decide (n - (j + 1) = 0)) := by
    rw [show isa.eval (.nonzero .x .x9) s'' = eval (.nonzero .x .x9) s'' from rfl, eval_nonzero, hz, bne,
      ofNat_beq_zero (by omega)]
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by rw [ev, hl]; rfl, ?_⟩
    rwa [show j + 1 = n by omega] at hc'
  · exact .inr ⟨by rw [ev]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

end

/-! ## A block to `out` -/

/-- The bytes of the derived key left before block `k + 1`, and how many of them it gives. -/
abbrev L (s₀ : State) (k : Nat) : Nat := ol s₀ - 32 * k
abbrev W (s₀ : State) (k : Nat) : Nat := min 32 (L s₀ k)

def BO1 (s₀ : State) (k : Nat) (s : State) : Prop :=
  AtT s₀ k s ∧ s.gpr .x9 = BitVec.ofNat 64 32 ∧ s.gpr .x10 = BitVec.ofNat 64 (L s₀ k / 32)

def BO2 (s₀ : State) (k : Nat) (s : State) : Prop :=
  AtT s₀ k s ∧ s.gpr .x9 = BitVec.ofNat 64 (W s₀ k)

/-- Before the bytes are copied. -/
structure BO3 (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Kp s₀ s (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (L s₀ k - W s₀ k)) (BitVec.ofNat 64 (cc s₀ - 1))
    (BitVec.ofNat 64 (64 + sl s₀)) (op s₀ + BitVec.ofNat 64 (32 * k))
  key : KeyR s₀ s.mem
  salt : Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)
  lt : 32 * k < ol s₀
  out : bytesAt s.mem (op s₀) (32 * k) = G s₀ k
  t : bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) 32 = Fk s₀ k
  x11 : s.gpr .x11 = sc s₀ + BitVec.ofNat 64 384
  x9 : s.gpr .x9 = BitVec.ofNat 64 (W s₀ k)

theorem shr5 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 5 = BitVec.ofNat 64 (a / 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bo1_ok {s₀ : State} {k : Nat} {s : State} (h : AtT s₀ k s) :
    WP isa (.block [.movz .x .x9 32 0, .lsr .x .x10 .x21 5]) s (BO1 s₀ k) := by
  obtain ⟨c, ht⟩ := h
  have := ol_lt s₀
  refine wp_run' rfl fun s' hg hm rd wr sp =>
    ⟨⟨c.regs' (c.regs.regs rd wr sp hm (by cs_keep hg)) hm, hm ▸ ht⟩, ?_, ?_⟩
  · rw [hg]; simp [upd]
  · rw [hg]; simp only [upd, reduceCtorEq, ite_true, ite_false, c.regs.x21]
    exact shr5 (by omega)

theorem bo2_ok {s₀ : State} {k : Nat} {s : State} (h : BO1 s₀ k s) :
    WP isa (.ite (.zero .x .x10) (.block [mov .x9 .x21]) (.block [])) s (BO2 s₀ k) := by
  obtain ⟨⟨c, ht⟩, h9, h10⟩ := h
  have := ol_lt s₀
  have ev : (s.gpr .x10 == 0) = decide (L s₀ k < 32) := by
    have : L s₀ k ≤ ol s₀ := Nat.sub_le _ _
    rw [h10, ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega
  refine WP.ite _ ((eval_zero s .x10).trans (by rw [ev])) (fun hb => ?_) (fun hb => WP.block_nil ⟨⟨c, ht⟩, ?_⟩)
  · refine wp_run' rfl fun s' hg hm rd wr sp =>
      ⟨⟨c.regs' (c.regs.regs rd wr sp hm (by cs_keep hg)) hm, hm ▸ ht⟩, ?_⟩
    have : L s₀ k < 32 := by simpa using hb
    rw [hg]; simp only [upd, ite_true, c.regs.x21]
    simp only [W, L] at this ⊢
    rw [Nat.min_eq_right (by omega)]; simp
  · have : ¬ L s₀ k < 32 := by simpa using hb
    rw [h9]; simp only [W, L] at this ⊢
    rw [Nat.min_eq_left (by omega)]

theorem bo3_ok {s₀ : State} {k : Nat} {s : State} (h : BO2 s₀ k s) :
    WP isa (.block [.sub .x .x21 .x21 .x9, .addImm .x .x11 .x19 384]) s (BO3 s₀ k) := by
  obtain ⟨⟨c, ht⟩, h9⟩ := h
  have := ol_lt s₀
  have kr := c.regs
  refine wp_run' rfl fun s' hg hm rd wr sp => ?_
  have cs : ∀ r, r ≠ .x21 → r ≠ .x11 → s'.gpr r = s.gpr r := fun r h1 h2 => by
    rw [hg]; simp [upd, h1, h2]
  refine ⟨⟨kr.base.regs rd wr sp (cs _ (by decide) (by decide)) (cs _ (by decide) (by decide))
      (cs _ (by decide) (by decide)) hm,
    (cs _ (by decide) (by decide)).trans kr.x20, ?_, (cs _ (by decide) (by decide)).trans kr.x22,
    (cs _ (by decide) (by decide)).trans kr.x23, (cs _ (by decide) (by decide)).trans kr.x24⟩,
    hm ▸ c.key, hm ▸ c.salt, c.lt, hm ▸ c.out, hm ▸ ht, ?_, ?_⟩
  · rw [hg]; simp only [upd, reduceCtorEq, ite_true, ite_false, kr.x21, h9]
    exact sub_ofNat (by simp only [W, L]; omega)
  · rw [hg]; simp [upd, kr.base.x19]
  · rw [hg]; simp [upd, h9]

/-! ## Copying `T` -/

theorem G_succ (s₀ : State) (k : Nat) : G s₀ (k + 1) = G s₀ k ++ Fk s₀ k := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- After the bytes are copied. -/
structure BO4 (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Kp s₀ s (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (L s₀ k - W s₀ k)) (BitVec.ofNat 64 (cc s₀ - 1))
    (BitVec.ofNat 64 (64 + sl s₀)) (op s₀ + BitVec.ofNat 64 (32 * k + W s₀ k))
  key : KeyR s₀ s.mem
  salt : Repr s.mem (sc s₀ + BitVec.ofNat 64 192) (xorPad (k0 s₀) ipad ++ S s₀)
  lt : 32 * k < ol s₀
  out : bytesAt s.mem (op s₀) (32 * k + W s₀ k) = G s₀ k ++ (Fk s₀ k).take (W s₀ k)
  glen : (G s₀ k).length = 32 * k
  fk : (Fk s₀ k).length = 32

/-- The derived key when the blocks are done. -/
def Done (s₀ : State) (s : State) : Prop :=
  Base s₀ s ∧ bytesAt s.mem (op s₀) (ol s₀) = (G s₀ ((ol s₀ + 31) / 32)).take (ol s₀)

/-- After block `k + 1`: done, or on to the next one. -/
structure Next (s₀ : State) (k : Nat) (s : State) : Prop where
  x21 : s.gpr .x21 = BitVec.ofNat 64 (L s₀ k - W s₀ k)
  done : L s₀ k - W s₀ k = 0 → Done s₀ s
  next : L s₀ k - W s₀ k ≠ 0 → Core s₀ (k + 1) s

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem bo4_ok {k : Nat} {s : State} (h : BO3 s₀ k s) : WP isa byteLoop s (BO4 s₀ k) := by
  have := ol_lt s₀
  have := h.lt
  have hW : W s₀ k ≤ 32 := Nat.min_le_left _ _
  have hW0 : 0 < W s₀ k := by simp only [W, L]; omega
  have hWL : 32 * k + W s₀ k ≤ ol s₀ := by simp only [W, L]; omega
  have hwr := h.regs.base.wr
  have hsub : Region.Sub ⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩ (outR s₀) := sub_offset (by omega) (by omega)
  refine WP.mono (copy_loop (a := sc s₀ + BitVec.ofNat 64 384) (b := op s₀ + BitVec.ofNat 64 (32 * k))
    (by omega) (fun i hi => by rw [add_ofNat]; exact hp.in_sc' hwr (by omega))
    (fun i hi => ⟨outR s₀, by rw [hwr, hp.wr]; simp, by
      rw [add_ofNat]; exact contains_offset (by omega) (by omega)⟩)
    ((hp.o_sR (o := 384) (n := W s₀ k) (by omega)).symm.sub_right hsub) hW0 h.x11 h.regs.x24 h.x9)
    fun s' c => ?_
  have f : Frame [⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩] s.mem s'.mem := by
    rw [c.mem]; exact copy_frame _ _ _ _
  have hd : ∀ {o n : Nat}, o + n ≤ 2048 → ∀ r ∈ [(⟨op s₀ + BitVec.ofNat 64 (32 * k), W s₀ k⟩ : Region)],
      Region.Disjoint (sR s₀ o n) r := fun hon r hr => by
    rw [List.mem_singleton.1 hr]; exact (hp.o_sR hon).symm.sub_right hsub
  have fk : (Fk s₀ k).length = 32 := by rw [← h.t, Proof.Hmac.X86_64.bytesAt_length]
  have glen : (G s₀ k).length = 32 * k := by rw [← h.out, Proof.Hmac.X86_64.bytesAt_length]
  have kp := h.regs
  have fw : Frame (wk s₀) s.mem s'.mem :=
    f.sub fun r hr => ⟨outR s₀, by simp, by rw [List.mem_singleton.1 hr]; exact hsub⟩
  refine ⟨⟨kp.base.step hp c.rd c.wr c.sp (c.keep _ (by decide) (by decide) (by decide) (by decide))
      (c.keep _ (by decide) (by decide) (by decide) (by decide))
      (c.keep _ (by decide) (by decide) (by decide) (by decide)) fw,
      (c.keep _ (by decide) (by decide) (by decide) (by decide)).trans kp.x20,
      (c.keep _ (by decide) (by decide) (by decide) (by decide)).trans kp.x21,
      (c.keep _ (by decide) (by decide) (by decide) (by decide)).trans kp.x22,
      (c.keep _ (by decide) (by decide) (by decide) (by decide)).trans kp.x23,
      by rw [c.x24, add_ofNat]⟩,
    ⟨repr_frame f (hd (o := 0) (n := 96) (by omega)) h.key.1, repr_frame f (hd (o := 96) (n := 96) (by omega)) h.key.2⟩,
    repr_frame f (hd (o := 192) (n := 96) (by omega)) h.salt, h.lt, ?_, glen, fk⟩
  have e := Proof.Sha256.Stream.bytesAt_writeBytes s.mem (op s₀) (32 * k)
    (bytesAt s.mem (sc s₀ + BitVec.ofNat 64 384) (W s₀ k)) (by rw [Proof.Hmac.X86_64.bytesAt_length]; omega)
  rw [Proof.Hmac.X86_64.bytesAt_length] at e
  rw [c.mem, e, h.out, ← h.t, bytesAt_take _ _ hW]

omit hp in
theorem bo5_ok {k : Nat} {s : State} (h : BO4 s₀ k s) :
    WP isa (.block [.addImm .x .x20 .x20 1]) s (Next s₀ k) := by
  have := ol_lt s₀
  have := h.lt
  have kr := h.regs
  refine wp_run' rfl fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  have x21 : s₁.gpr .x21 = BitVec.ofNat 64 (L s₀ k - W s₀ k) := by rw [g₁]; simp [upd, kr.x21]
  have base : Base s₀ s₁ := kr.base.regs rd₁ wr₁ sp₁ (by rw [g₁]; simp [upd]) (by rw [g₁]; simp [upd])
    (by rw [g₁]; simp [upd]) m₁
  refine ⟨x21, fun hl => ?_, fun hl => ?_⟩
  · have hW : W s₀ k = ol s₀ - 32 * k := by simp only [W, L] at hl ⊢; omega
    have hk : (ol s₀ + 31) / 32 = k + 1 := by simp only [W, L] at hl; omega
    have hol : ol s₀ = 32 * k + W s₀ k := by omega
    have e1 : bytesAt s₁.mem (op s₀) (ol s₀) = G s₀ k ++ (Fk s₀ k).take (W s₀ k) := by
      rw [m₁, hol]; exact h.out
    refine ⟨base, ?_⟩
    rw [e1, hk, G_succ, List.take_append, List.take_of_length_le (l := G s₀ k) (by rw [h.glen]; omega), h.glen, hW]
  · have hL : 32 * (k + 1) < ol s₀ := by simp only [W, L] at hl; omega
    have hW : W s₀ k = 32 := by simp only [W, L]; omega
    have hk : 32 * (k + 1) = 32 * k + W s₀ k := by omega
    refine ⟨⟨base, ?_, ?_, ?_, ?_, ?_⟩, m₁ ▸ h.key, m₁ ▸ h.salt, by omega, ?_⟩
    · rw [g₁]; simp only [upd, ite_true, kr.x20]; exact (BitVec.ofNat_add (k + 1) 1).symm
    · rw [x21, show L s₀ k - W s₀ k = ol s₀ - 32 * (k + 1) by simp only [W, L]; omega]
    · rw [g₁]; simp [upd, kr.x22]
    · rw [g₁]; simp [upd, kr.x23]
    · rw [g₁]; simp [upd, kr.x24, hk]
    · rw [m₁, hk, h.out, G_succ, hW, List.take_of_length_le (by rw [h.fk])]

theorem blockOut_ok {k : Nat} {s : State} (h : AtT s₀ k s) : WP isa blockOut s (Next s₀ k) :=
  WP.seq (WP.mono (bo1_ok h) fun _ h1 => WP.seq (WP.mono (bo2_ok h1) fun _ h2 => WP.seq (WP.mono (bo3_ok h2)
    fun _ h3 => WP.seq (WP.mono (bo4_ok hp h3) fun _ h4 => bo5_ok h4))))

theorem body_ok {k : Nat} {s : State} (h : Core s₀ k s) : WP isa block s (Next s₀ k) :=
  WP.seq (WP.mono (bu_ok hp h) fun _ h1 => WP.seq (WP.mono (bt_ok hp h1) fun _ h2 => blockOut_ok hp h2))

omit hp in
theorem Next.cond {k : Nat} {s : State} (h : Next s₀ k s) :
    isa.eval (.nonzero .x .x21) s = some (!decide (L s₀ k - W s₀ k = 0)) := by
  have := ol_lt s₀
  have : L s₀ k ≤ ol s₀ := Nat.sub_le _ _
  rw [show isa.eval (.nonzero .x .x21) s = AArch64.eval (.nonzero .x .x21) s from rfl, eval_nonzero, h.x21, bne,
    ofNat_beq_zero (by omega)]

theorem loop_ok {s : State} (h : Core s₀ 0 s) : WP isa (.loop block (.nonzero .x .x21)) s (Done s₀) := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = ol s₀ - 32 * k ∧ Core s₀ k t) ?_ (ol s₀) s ⟨0, by simp, h⟩
  clear h
  rintro n t ⟨k, rfl, hc⟩
  refine WP.mono (body_ok hp hc) fun s' hs' => ?_
  by_cases hl : L s₀ k - W s₀ k = 0
  · exact .inl ⟨by rw [hs'.cond, hl]; rfl, hs'.done hl⟩
  · have := (hs'.next hl).lt
    exact .inr ⟨by rw [hs'.cond]; simp [hl], ol s₀ - 32 * (k + 1), by omega, k + 1, rfl, hs'.next hl⟩

end

end VG.Proof.Pbkdf2.AArch64Derive
