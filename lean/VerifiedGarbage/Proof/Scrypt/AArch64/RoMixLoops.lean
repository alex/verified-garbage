import VerifiedGarbage.Proof.Scrypt.AArch64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixLoops

/-!
# scryptROMix on AArch64: the small loops

Untrusted: everything here is checked by Lean. The word copy (`copyLoop`),
the word exclusive-or (`xorLoop`) and the computation of `2 N` by doubling
(`nLoop`). The memory lemmas are the x86-64 proof's
(`Proof/Scrypt/X86_64/RoMixLoops.lean`), which are about memory only.
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_add wp_sub wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero ofNat_pred sub_beq)
open VG.Proof.Scrypt.AArch64.BlockMix (wp_eor)
open VG.Proof.Scrypt.X86_64.BlockMix (toNat_ofNat_lt add_ofNat)

/-! ## Arithmetic -/

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega), Nat.sub_sub]

theorem dec_ne {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  rw [bne, ofNat_beq_zero (by omega)]
  by_cases h : k + 1 = n
  · simp only [h, Nat.sub_self, decide_true, Bool.not_true, ne_eq, not_true_eq_false, decide_false]
  · simp only [show n - (k + 1) ≠ 0 by omega, decide_false, Bool.not_false, ne_eq, h,
      not_false_eq_true, decide_true]

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (8 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop on `cbnz cr` that runs its body `n > 0` times: the
register is zero exactly after the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by
    show VG.AArch64.eval (.nonzero .x cr) s' = _
    rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.gpr r = s.gpr r
  x9 : t.gpr .x9 = src + BitVec.ofNat 64 (8 * k)
  x10 : t.gpr .x10 = dst + BitVec.ofNat 64 (8 * k)
  x11 : t.gpr .x11 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block [.ldr .x .x12 .x9 0, .str .x .x12 .x10 0, .addImm .x .x9 .x9 8,
      .addImm .x .x10 .x10 8, .subImm .x .x11 .x11 1]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ (t'.gpr .x11 != 0) = decide (k + 1 ≠ n) := by
  refine wp_ldr (a := src + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [h.x9, add_zero'])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_str (a := dst + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.x10, add_zero'])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ u₂ => ?_
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ =>
    wp_subImm (by decide) fun t₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x12 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
  have e11 : t₅.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.x11, dec_count hk]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], fun r h9 h10 h11 h12 => ?_, ?_, ?_, e11, ?_⟩, ?_⟩
  · rw [u₅.other r h11, u₄.other r h10, u₃.other r h9, g r h12, h.other r h9 h10 h11 h12]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.x9, next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.x10, next_ptr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Hmac.X86_64.copy_mem s.mem src dst k 8
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)
  · rw [e11, dec_ne hk (by omega)]

/-- `copyLoop` copies `8 n` bytes from `x9` to `x10` (`x11 = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (h9 : s.gpr .x9 = src) (h10 : s.gpr .x10 = dst) (h11 : s.gpr .x11 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h9], by rw [ofNat_zero_add, h10],
    by rw [h11, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
    t.gpr r = s.gpr r
  x9 : t.gpr .x9 = x + BitVec.ofNat 64 (8 * k)
  x10 : t.gpr .x10 = y + BitVec.ofNat 64 (8 * k)
  x11 : t.gpr .x11 = d + BitVec.ofNat 64 (8 * k)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * k)) (bytesAt s.mem y (8 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.ldr .x .x13 .x9 0, .ldr .x .x14 .x10 0, .logic .eor .x .x13 .x13 .x14,
      .str .x .x13 .x11 0, .addImm .x .x9 .x9 8, .addImm .x .x10 .x10 8, .addImm .x .x11 .x11 8,
      .subImm .x .x12 .x12 1]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ (t'.gpr .x12 != 0) = decide (k + 1 ≠ n) := by
  refine wp_ldr (a := x + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [h.x9, add_zero'])
    (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_ldr (a := y + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.x10, add_zero'])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_eor fun t₃ u₃ => ?_
  refine wp_str (a := d + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x11,
      add_zero'])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ u₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ =>
    wp_addImm (by decide) fun t₇ u₇ => wp_subImm (by decide) fun t₈ u₈ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x13 → r ≠ .x14 → t₄.gpr r = t.gpr r := fun r h13 h14 => by
    rw [u₄.gpr, u₃.other r h13, u₂.other r h14, u₁.other r h13]
  have e12 : t₈.gpr .x12 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x12, dec_count hk]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h9 h10 h11 h12 h13 h14 => ?_, ?_, ?_, ?_, e12, ?_⟩, ?_⟩
  · rw [u₈.other r h12, u₇.other r h11, u₆.other r h10, u₅.other r h9, g r h13 h14,
      h.other r h9 h10 h11 h12 h13 h14]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g _ (by decide) (by decide), h.x9, next_ptr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x10, next_ptr]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.x11, next_ptr]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .x13 (by decide), u₂.gpr,
      u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact Proof.Scrypt.X86_64.RoMix.xor_mem s.mem hk hlt hdx hdy
  · rw [e12, dec_ne hk (by omega)]

/-- `xorLoop` writes `[x9] xor [x10]` to `x11`, `8 n` bytes (`x12 = n > 0` words). -/
theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (h9 : s.gpr .x9 = x) (h10 : s.gpr .x10 = y) (h11 : s.gpr .x11 = d)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, h9],
    by rw [ofNat_zero_add, h10], by rw [ofNat_zero_add, h11], by rw [h12, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .x9 → r' ≠ .x10 → r' ≠ .x12 → t.gpr r' = s.gpr r'
  x9 : t.gpr .x9 = BitVec.ofNat 64 (r * 2 ^ k)
  x10 : t.gpr .x10 = BitVec.ofNat 64 (2 ^ k)

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.add .x .x9 .x9 .x9, .add .x .x10 .x10 .x10, .sub .x .x12 .x9 .x11]) t
      fun t' => NInv s r (k + 1) t' ∧ (t'.gpr .x12 != 0) = decide (k + 1 ≠ e + 1) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_sub fun t₃ u₃ => WP.block_nil ?_
  have ax : t₂.gpr .x9 = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.x9, Proof.Scrypt.X86_64.RoMix.dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₃.mem, u₂.mem, u₁.mem, h.mem],
    fun r' h9 h10 h12 => ?_, by rw [u₃.other _ (by decide), ax], ?_⟩, ?_⟩
  · rw [u₃.other r' h12, u₂.other r' h10, u₁.other r' h9, h.other r' h9 h10 h12]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x10, ← Nat.one_mul (2 ^ k),
      Proof.Scrypt.X86_64.RoMix.dbl_pow, Nat.one_mul]
  · rw [u₃.gpr, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide) (by decide), h11, bne, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, Bool.not_false, ne_eq, hh, not_false_eq_true, decide_true]

/-- `nLoop` doubles `x9` (from `r`) and `x10` (from 1) until `x9 = x11 = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 r) (h10 : s.gpr .x10 = 1)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .x9 → r' ≠ .x10 → r' ≠ .x12 → s'.gpr r' = s.gpr r') ∧
      s'.gpr .x10 = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h11 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.sp, h.mem, h.other, h.x10⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, by rw [h9, Nat.pow_zero, Nat.mul_one],
    by rw [h10]; rfl⟩

end VG.Proof.Scrypt.AArch64.RoMix
