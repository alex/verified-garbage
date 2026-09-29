import VerifiedGarbage.Proof.Scrypt.Arm.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixLoops

/-!
# scryptROMix on 32-bit ARM: the small loops

Untrusted: everything here is checked by Lean. The word copy (`copyLoop`),
the word exclusive-or (`xorLoop`), the multiplication by shifts and adds
(`mulLoop`, as on x86-64: the model has no multiplication) and the
computation of `2 N` by doubling (`nLoop`). Words are 4 bytes, and pointers
32 bits, which address memory by their zero extensions.
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd wp_mov wp_add wp_and wp_subs wp_cmp wp_ldr wp_str
  op2_reg op2_imm op2_lsr eval_ne ofNat_beq_zero sub_beq)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Scrypt.X86_64.BlockMix (sub_off bytesAt_add bytesAt_length bytesAt_writeBytes_sep
  xorBytes_length)

/-! ## Arithmetic -/

theorem add_zero32 (p : BitVec 32) : p + BitVec.ofNat 32 0 = p := BitVec.add_zero _

/-- A pointer advanced by one word. -/
theorem next32 (p : BitVec 32) (k : Nat) :
    p + BitVec.ofNat 32 (4 * k) + 4 = p + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [add32_lit, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [ofNat_pred32 (by omega), Nat.sub_sub]

theorem dec_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem cmp0 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a - 0 == 0) = decide (a = 0) := by
  rw [show BitVec.ofNat 32 a - 0 = BitVec.ofNat 32 a from BitVec.sub_zero _]
  exact ofNat_beq_zero h

theorem ofNat_zero_add32 (p : BitVec 32) : p + BitVec.ofNat 32 (4 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-- A word of a region, as an address. -/
theorem word_addr {p : BitVec 32} {n k : Nat} (hp : p.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    State.addr (p + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) =
      State.addr p + BitVec.ofNat 64 (4 * k) := by
  rw [add_zero32, addr_add (by omega)]

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with Z set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.z = decide (k + 1 = n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by rw [← hz]; exact eval_ne s'
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r
  r0 : t.gpr .r0 = src + BitVec.ofNat 32 (4 * k)
  r1 : t.gpr .r1 = dst + BitVec.ofNat 32 (4 * k)
  r2 : t.gpr .r2 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (State.addr dst) (bytesAt s.mem (State.addr src) (4 * k))

theorem copy_step {s : State} {src dst : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨State.addr src, 4 * n⟩ ⟨State.addr dst, 4 * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : CopyInv s src dst n k t) :
    WP isa (.block [.ldr .r3 .r0 0, .str .r3 .r1 0, .dp .add .r0 .r0 (.imm 4),
      .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.z = decide (k + 1 = n) := by
  refine wp_ldr (a := State.addr src + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [h.r0, word_addr fs hk]) (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_str (a := State.addr dst + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, word_addr fd hk])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r3 → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
  have e2 : t₄.gpr .r2 = BitVec.ofNat 32 (n - k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.r2]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], fun r h0 h1 h2 h3 => ?_, ?_, ?_,
    by rw [u₅.gpr, e2, dec_count hk], ?_⟩, by rw [z₅, e2, dec_z hk hn]⟩
  · rw [u₅.other r h2, u₄.other r h1, u₃.other r h0, g r h3, h.other r h0 h1 h2 h3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.r0, next32]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.r1, next32]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Hmac.X86_64.copy_mem s.mem _ _ k 4
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)

/-- `copyLoop` copies `4 n` bytes from `r0` to `r1` (`r2 = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .r0 = src) (h1 : s.gpr .r1 = dst) (h2 : s.gpr .r2 = BitVec.ofNat 32 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨State.addr src, 4 * n⟩ ⟨State.addr dst, 4 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr dst) (bytesAt s.mem (State.addr src) (4 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt fs fd hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [h2, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem4 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 4 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 4 * n⟩ ⟨x, 4 * n⟩) (hdy : Region.Disjoint ⟨d, 4 * n⟩ ⟨y, 4 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).writeW
      (d + BitVec.ofNat 64 (4 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (x + BitVec.ofNat 64 (4 * k)) 32 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (y + BitVec.ofNat 64 (4 * k)) 32) =
      writeBytes m d (xorBytes (bytesAt m x (4 * (k + 1))) (bytesAt m y (4 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length = 4 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor32, bytesAt_writeBytes_sep _ _ sx (by omega),
    bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (4 * k)) 4)
    (bytesAt m (y + BitVec.ofNat 64 (4 * k)) 4))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r
  r0 : t.gpr .r0 = x + BitVec.ofNat 32 (4 * k)
  r1 : t.gpr .r1 = y + BitVec.ofNat 32 (4 * k)
  r2 : t.gpr .r2 = d + BitVec.ofNat 32 (4 * k)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (State.addr d)
    (xorBytes (bytesAt s.mem (State.addr x) (4 * k)) (bytesAt s.mem (State.addr y) (4 * k)))

theorem xor_step {s : State} {x y d : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr x, 4 * n⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr y, 4 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.ldr .r12 .r0 0, .ldr .lr .r1 0, .dp .eor .r12 .r12 (.reg .lr), .str .r12 .r2 0,
      .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4),
      .subs .r3 .r3 (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.z = decide (k + 1 = n) := by
  refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [h.r0, word_addr fx hk]) (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_ldr (a := State.addr y + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, word_addr fy hk])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_str (a := State.addr d + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2,
      word_addr fd hk])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_add (op2_imm (by decide)) fun t₆ u₆ =>
    wp_add (op2_imm (by decide)) fun t₇ u₇ => wp_subs (op2_imm (by decide)) fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .lr → t₄.gpr r = t.gpr r := fun r h12 hlr => by
    rw [u₄.gpr, u₃.other r h12, u₂.other r hlr, u₁.other r h12]
  have e3 : t₇.gpr .r3 = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r3]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h0 h1 h2 h3 h12 hlr => ?_, ?_, ?_, ?_, by rw [u₈.gpr, e3, dec_count hk], ?_⟩,
    by rw [z₈, e3, dec_z hk hn]⟩
  · rw [u₈.other r h3, u₇.other r h2, u₆.other r h1, u₅.other r h0, g r h12 hlr,
      h.other r h0 h1 h2 h3 h12 hlr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g _ (by decide) (by decide), h.r0, next32]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r1, next32]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide) (by decide), h.r2, next32]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other .r12 (by decide), u₂.gpr,
      u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem4 s.mem hk (by omega) hdx hdy

/-- `xorLoop` writes `[r0] xor [r1]` to `r2`, `4 n` bytes (`r3 = n > 0` words). -/
theorem xorLoop_ok {s : State} {x y d : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = d)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr x, 4 * n⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 4 * n⟩ ⟨State.addr y, 4 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr d)
        (xorBytes (bytesAt s.mem (State.addr x) (4 * n)) (bytesAt s.mem (State.addr y) (4 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt fx fy fd hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [ofNat_zero_add32, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- `r0 = m`, and `r1 + r0 * r2` is still `a + j c`. -/
structure MulInv (s : State) (j c : Nat) (a : BitVec 32) (m : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r
  lt : m < 2 ^ 32
  r0 : t.gpr .r0 = BitVec.ofNat 32 m
  sum : t.gpr .r1 + BitVec.ofNat 32 m * t.gpr .r2 = a + BitVec.ofNat 32 (j * c)

theorem and_one_z {m : Nat} (h : m < 2 ^ 32) :
    ((BitVec.ofNat 32 m &&& 1) - 0 == 0) = decide (m % 2 = 0) := by
  have e : BitVec.ofNat 32 m &&& 1 = BitVec.ofNat 32 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : m % 2 < 2 ^ 32), show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod]
  rw [e, cmp0 (by omega)]

/-- The invariant across one iteration: `r1` gains `r2` if `m` is odd. -/
theorem mul_sum (d r : BitVec 32) (m : Nat) :
    (d + (if m % 2 = 1 then r else 0)) + BitVec.ofNat 32 (m / 2) * (r + r) =
      d + BitVec.ofNat 32 m * r := by
  have e : BitVec.ofNat 32 m = BitVec.ofNat 32 (m / 2) + BitVec.ofNat 32 (m / 2) +
      BitVec.ofNat 32 (m % 2) := by
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
  by_cases h : m % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [e, h, show BitVec.ofNat 32 1 = 1 from rfl]; grind
  · simp only [h, ↓reduceIte]
    rw [e, show m % 2 = 0 by omega, show BitVec.ofNat 32 0 = 0 from rfl]; grind

/-- The conditional add: `r1 ← r1 + r2` if `r0` is odd. -/
theorem mul_ite {m : Nat} {t : State} (hz : t.z = decide (m % 2 = 0)) :
    WP isa (.ite .ne (.block [.dp .add .r1 .r1 (.reg .r2)]) (.block [])) t fun t' =>
      Upd t t' .r1 (t.gpr .r1 + if m % 2 = 1 then t.gpr .r2 else 0) := by
  refine WP.ite (!decide (m % 2 = 0)) (by rw [← hz]; exact eval_ne t)
    (fun hb => wp_add (op2_reg _ _) fun t₁ u₁ => WP.block_nil ?_) (fun hb => WP.block_nil ?_)
  · have : m % 2 = 1 := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hb; omega
    simp only [this, ↓reduceIte]; exact u₁
  · have : ¬ m % 2 = 1 := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hb; omega
    simp only [this, ↓reduceIte]
    rw [show t.gpr .r1 + 0 = t.gpr .r1 from BitVec.add_zero _]
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem mul_step {s : State} {j c : Nat} {a : BitVec 32} {m : Nat} {t : State}
    (h : MulInv s j c a m t) :
    WP isa (.seq (.block [.dp .and .r3 .r0 (.imm 1), .cmp .r3 (.imm 0)]) <|
      .seq (.ite .ne (.block [.dp .add .r1 .r1 (.reg .r2)]) (.block []))
        (.block [.dp .add .r2 .r2 (.reg .r2), .mov .r0 (.shifted .r0 .lsr 1), .cmp .r0 (.imm 0)])) t
      fun t' => MulInv s j c a (m / 2) t' ∧ t'.z = decide (m / 2 = 0) := by
  refine WP.seq (wp_and (op2_imm (by decide)) fun t₁ u₁ =>
    wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  have hz : t₂.z = decide (m % 2 = 0) := by
    rw [z₂, u₁.gpr, h.r0, and_one_z h.lt]
  refine WP.seq (WP.mono (mul_ite hz) fun t₃ u₃ => ?_)
  refine wp_add (op2_reg _ _) fun t₄ u₄ => wp_mov (op2_lsr (by decide)) fun t₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun t₆ f₆ z₆ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r3 → t₂.gpr r = t.gpr r := fun r hr => by rw [f₂.gpr, u₁.other r hr]
  have ax₄ : t₄.gpr .r0 = BitVec.ofNat 32 m := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), h.r0]
  have e0 : t₆.gpr .r0 = BitVec.ofNat 32 (m / 2) := by
    rw [f₆.gpr, u₅.gpr, ax₄, shr_ofNat32 _ h.lt, Nat.pow_one]
  refine ⟨⟨by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, f₂.rd, u₁.rd, h.rd],
    by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, f₂.wr, u₁.wr, h.wr],
    by rw [f₆.sp, u₅.sp, u₄.sp, u₃.sp, f₂.sp, u₁.sp, h.sp],
    by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, f₂.mem, u₁.mem, h.mem],
    fun r h0 h1 h2 h3 => ?_, by have := h.lt; omega, e0, ?_⟩, ?_⟩
  · rw [f₆.gpr, u₅.other r h0, u₄.other r h2, u₃.other r h1, g₂ r h3, h.other r h0 h1 h2 h3]
  · rw [f₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₄.other _ (by decide),
      u₃.gpr, u₃.other _ (by decide), g₂ _ (by decide), g₂ _ (by decide), mul_sum, h.sum]
  · rw [z₆, u₅.gpr, ax₄, shr_ofNat32 _ h.lt, Nat.pow_one, cmp0 (by have := h.lt; omega)]

/-- `mulLoop` adds `r0 * r2` to `r1` (modulo 2^32), for any `r0`. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : BitVec 32} (hj : j < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 j) (h1 : s.gpr .r1 = a) (h2 : s.gpr .r2 = BitVec.ofNat 32 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r1 = a + BitVec.ofNat 32 (j * c) := by
  refine WP.loop (M := isa) (MulInv s j c a) ?_ j s
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, hj, h0, by rw [h1, h2, BitVec.ofNat_mul]⟩
  intro m t h
  refine WP.mono (mul_step h) fun t' ⟨h', hz⟩ => ?_
  have he : isa.eval .ne t' = some (!decide (m / 2 = 0)) := by rw [← hz]; exact eval_ne t'
  by_cases hl : m / 2 = 0
  · refine .inl ⟨by rw [he]; simp [hl], h'.rd, h'.wr, h'.sp, h'.mem, h'.other, ?_⟩
    have := h'.sum
    rwa [hl, BitVec.zero_mul, BitVec.add_zero] at this
  · exact .inr ⟨by rw [he]; simp [hl], m / 2, by omega, h'⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .r0 → r' ≠ .r1 → t.gpr r' = s.gpr r'
  r0 : t.gpr .r0 = BitVec.ofNat 32 (r * 2 ^ k)
  r1 : t.gpr .r1 = BitVec.ofNat 32 (2 ^ k)

theorem dbl_pow32 (x k : Nat) : BitVec.ofNat 32 (x * 2 ^ k) + BitVec.ofNat 32 (x * 2 ^ k) =
    BitVec.ofNat 32 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.dp .add .r0 .r0 (.reg .r0), .dp .add .r1 .r1 (.reg .r1), .cmp .r0 (.reg .r2)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.z = decide (k + 1 = e + 1) := by
  refine wp_add (op2_reg _ _) fun t₁ u₁ => wp_add (op2_reg _ _) fun t₂ u₂ =>
    wp_cmp (op2_reg _ _) fun t₃ f₃ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .r0 = BitVec.ofNat 32 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.r0, dbl_pow32]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [f₃.sp, u₂.sp, u₁.sp, h.sp], by rw [f₃.mem, u₂.mem, u₁.mem, h.mem],
    fun r' h0 h1 => ?_, by rw [f₃.gpr, ax], ?_⟩, ?_⟩
  · rw [f₃.gpr, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1]
  · rw [f₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r1, ← Nat.one_mul (2 ^ k), dbl_pow32, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), h2, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, hh]

/-- `nLoop` doubles `r0` (from `r`) and `r1` (from 1) until `r0 = r2 = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 r) (h1 : s.gpr .r1 = 1)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .r0 → r' ≠ .r1 → s'.gpr r' = s.gpr r') ∧
      s'.gpr .r1 = BitVec.ofNat 32 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.sp, h.mem, h.other, h.r1⟩
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.Arm.RoMix
