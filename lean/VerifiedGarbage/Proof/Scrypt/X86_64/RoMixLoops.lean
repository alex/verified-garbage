import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: the small loops

Untrusted: everything here is checked by Lean. The word copy (`copyLoop`),
the word exclusive-or (`xorLoop`), the multiplication by shifts and adds
(`mulLoop`) and the computation of `2 N` by doubling (`nLoop`).
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Sha1.X86_64.Stream (Upd wp_movm wp_store wp_add wp_addi wp_subi wp_cmp ofNat_pred
  ofNat_beq_zero sub_beq)
open VG.Proof.Scrypt.X86_64.BlockMix (ea_at toNat_ofNat_lt add_ofNat sub_off writeW_xor wp_xorm
  bytesAt_add bytesAt_length bytesAt_writeBytes_sep xorBytes_length)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `test d, imm`: only ZF matters here. -/
theorem wp_testi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  Proof.Sha1.X86_64.Stream.WP.cons rfl (k _ rfl rfl rfl rfl rfl)

/-- `shr d, 1`. -/
theorem wp_shr1 {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d >>> 1) → s'.zf = some (s.gpr d >>> 1 == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d 1 :: is)) s Q :=
  Proof.Sha1.X86_64.Stream.WP.cons rfl
    (k _ ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩ rfl)

end

theorem ea_at0 (s : State) (b : Reg) : s.ea (at_ b 0) = s.gpr b := by
  rw [ea_at]; exact BitVec.add_zero _

theorem sx8 : (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 := by decide

theorem sx1 : (1 : BitVec 32).signExtend 64 = 1 := by decide

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + (8 : BitVec 32).signExtend 64 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [sx8, add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [sx1, ofNat_pred (by omega), Nat.sub_sub]

theorem dec_zf {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (8 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = src + BitVec.ofNat 64 (8 * k)
  rsi : t.gpr .rsi = dst + BitVec.ofNat 64 (8 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .store (at_ .rsi 0) .rax,
      .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := src + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store (a := dst + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₂.gpr r = t.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha hdi hsi hcx => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other r hcx, u₄.other r hsi, u₃.other r hdi, g r ha, h.other r ha hdi hsi hcx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.rdi, next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.rsi, next_ptr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx, dec_count hk]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Hmac.X86_64.copy_mem s.mem src dst k 8
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx,
      dec_zf hk (by omega)]

/-- `copyLoop` copies `8 n` bytes from `rdi` to `rsi` (`rcx = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = src) (hsi : s.gpr .rsi = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_) fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [hcx, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 8 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).writeW
      (d + BitVec.ofNat 64 (8 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (x + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (y + BitVec.ofNat 64 (8 * k)) 64) =
      writeBytes m d (xorBytes (bytesAt m x (8 * (k + 1))) (bytesAt m y (8 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length = 8 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (8 * k)) 8)
    (bytesAt m (y + BitVec.ofNat 64 (8 * k)) 8))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = x + BitVec.ofNat 64 (8 * k)
  rsi : t.gpr .rsi = y + BitVec.ofNat 64 (8 * k)
  r8 : t.gpr .r8 = d + BitVec.ofNat 64 (8 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * k)) (bytesAt s.mem y (8 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .alu .xor .rax (.mem (at_ .rsi 0)),
      .store (at_ .r8 0) .rax, .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8),
      .alu .add .r8 (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := x + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_xorm (a := y + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_store (a := d + BitVec.ofNat 64 (8 * k))
    (by rw [ea_at0, u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ =>
    wp_subi fun t₇ u₇ z₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃, u₂.other r hr, u₁.other r hr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr],
    fun r ha hdi hsi h8 hcx => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other r hcx, u₆.other r h8, u₅.other r hsi, u₄.other r hdi, g r ha,
      h.other r ha hdi hsi h8 hcx]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g _ (by decide), h.rdi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g _ (by decide), h.rsi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.r8, next_ptr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_count hk]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem s.mem hk hlt hdx hdy
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_zf hk (by omega)]

/-- `xorLoop` writes `[rdi] xor [rsi]` to `r8`, `8 n` bytes. -/
theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = x) (hsi : s.gpr .rsi = y) (hr8 : s.gpr .r8 = d)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [ofNat_zero_add, hr8], by rw [hcx, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- `rax = m`, and `rdx + rax * rcx` is still `a + j c`. -/
structure MulInv (s : State) (j c : Nat) (a : Addr) (m : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  lt : m < 2 ^ 64
  rax : t.gpr .rax = BitVec.ofNat 64 m
  sum : t.gpr .rdx + BitVec.ofNat 64 m * t.gpr .rcx = a + BitVec.ofNat 64 (j * c)

theorem and_one_beq {m : Nat} (h : m < 2 ^ 64) :
    (BitVec.ofNat 64 m &&& (1 : BitVec 32).signExtend 64 == 0) = decide (m % 2 = 0) := by
  have e : BitVec.ofNat 64 m &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [sx1, BitVec.toNat_and, toNat_ofNat_lt h, toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  rw [e, ofNat_beq_zero (by omega)]

theorem shr_one {m : Nat} (h : m < 2 ^ 64) : BitVec.ofNat 64 m >>> 1 = BitVec.ofNat 64 (m / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow,
    Nat.pow_one]

/-- The invariant across one iteration: `rdx` gains `rcx` if `m` is odd. -/
theorem mul_sum (d r : BitVec 64) (m : Nat) :
    (d + (if m % 2 = 1 then r else 0)) + BitVec.ofNat 64 (m / 2) * (r + r) =
      d + BitVec.ofNat 64 m * r := by
  have e : BitVec.ofNat 64 m = BitVec.ofNat 64 (m / 2) + BitVec.ofNat 64 (m / 2) +
      BitVec.ofNat 64 (m % 2) := by
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
  by_cases h : m % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [e, h, show BitVec.ofNat 64 1 = 1 from rfl]; grind
  · simp only [h, ↓reduceIte]
    rw [e, show m % 2 = 0 by omega, show BitVec.ofNat 64 0 = 0 from rfl]; grind

/-- The conditional add: `rdx ← rdx + rcx` if `rax` is odd. -/
theorem mul_ite {m : Nat} (hm : m < 2 ^ 64) {t : State} (hax : t.gpr .rax = BitVec.ofNat 64 m)
    (hz : t.zf = some (t.gpr .rax &&& (1 : BitVec 32).signExtend 64 == 0)) :
    WP isa (.ite .ne (.block [.alu .add .rdx (.reg .rcx)]) (.block [])) t fun t' =>
      Upd t t' .rdx (t.gpr .rdx + if m % 2 = 1 then t.gpr .rcx else 0) := by
  refine WP.ite (!decide (m % 2 = 0)) (by simp only [eval, hz, hax, and_one_beq hm, Option.map_some])
    (fun hb => wp_add fun t₁ u₁ => WP.block_nil ?_) (fun hb => WP.block_nil ?_)
  · have : m % 2 = 1 := by simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hb; omega
    simp only [this, ↓reduceIte]; exact u₁
  · have : ¬ m % 2 = 1 := by simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hb; omega
    simp only [this, ↓reduceIte]
    rw [show t.gpr .rdx + 0 = t.gpr .rdx from BitVec.add_zero _]
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem mul_step {s : State} {j c : Nat} {a : Addr} {m : Nat} {t : State} (h : MulInv s j c a m t) :
    WP isa (.seq (.block [.alu .test .rax (.imm 1)]) <|
      .seq (.ite .ne (.block [.alu .add .rdx (.reg .rcx)]) (.block []))
        (.block [.alu .add .rcx (.reg .rcx), .shift .shr .rax 1])) t
      fun t' => MulInv s j c a (m / 2) t' ∧ t'.zf = some (decide (m / 2 = 0)) := by
  refine WP.seq (wp_testi fun t₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have ax₁ : t₁.gpr .rax = BitVec.ofNat 64 m := by rw [g₁, h.rax]
  refine WP.seq (WP.mono (mul_ite h.lt ax₁ (by rw [z₁, g₁])) fun t₂ u₂ => ?_)
  refine wp_add fun t₃ u₃ => wp_shr1 fun t₄ u₄ z₄ => WP.block_nil ?_
  have ax₃ : t₃.gpr .rax = BitVec.ofNat 64 m := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), ax₁]
  refine ⟨⟨by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr],
    by rw [u₄.mem, u₃.mem, u₂.mem, m₁, h.mem], fun r ha hd hc => ?_, by have := h.lt; omega, ?_, ?_⟩, ?_⟩
  · rw [u₄.other r ha, u₃.other r hc, u₂.other r hd, g₁, h.other r ha hd hc]
  · rw [u₄.gpr, ax₃, shr_one h.lt]
  · rw [u₄.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr,
      u₂.other _ (by decide), g₁, mul_sum, h.sum]
  · rw [z₄, ax₃, shr_one h.lt, ofNat_beq_zero (by have := h.lt; omega)]

/-- `mulLoop` adds `rax * rcx` to `rdx` (modulo 2^64), for any `rax`. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : Addr} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = a) (hcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.gpr .rdx = a + BitVec.ofNat 64 (j * c) := by
  refine WP.loop (M := isa) (MulInv s j c a) ?_ j s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, hj, hax, by rw [hdx, hcx, BitVec.ofNat_mul]⟩
  intro m t h
  refine WP.mono (mul_step h) fun t' ⟨h', hz⟩ => ?_
  by_cases hl : m / 2 = 0
  · refine .inl ⟨by simp [eval, hz, hl], h'.rd, h'.wr, h'.mem, h'.other, ?_⟩
    have := h'.sum
    rwa [hl, BitVec.zero_mul, BitVec.add_zero] at this
  · exact .inr ⟨by simp [eval, hz, hl], m / 2, by omega, h'⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .rax → r' ≠ .rdx → t.gpr r' = s.gpr r'
  rax : t.gpr .rax = BitVec.ofNat 64 (r * 2 ^ k)
  rdx : t.gpr .rdx = BitVec.ofNat 64 (2 ^ k)

theorem dbl_pow (x k : Nat) : BitVec.ofNat 64 (x * 2 ^ k) + BitVec.ofNat 64 (x * 2 ^ k) =
    BitVec.ofNat 64 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.alu .add .rax (.reg .rax), .alu .add .rdx (.reg .rdx),
      .alu .cmp .rax (.reg .rcx)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .rax = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.rax, dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
    by rw [m₃, u₂.mem, u₁.mem, h.mem], fun r' ha hd => ?_, by rw [g₃, ax], ?_⟩, ?_⟩
  · rw [g₃, u₂.other r' hd, u₁.other r' ha, h.other r' ha hd]
  · rw [g₃, u₂.gpr, u₁.other _ (by decide), h.rdx, ← Nat.one_mul (2 ^ k), dbl_pow, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide), h.other _ (by decide) (by decide),
      hcx, sub_beq (by omega) hlt]
    refine congrArg some (decide_eq_decide.mpr ⟨fun hh => ?_, fun hh => by rw [hh]⟩)
    exact (Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr hh)

/-- `nLoop` doubles `rax` (from `r`) and `rdx` (from 1) until `rax = rcx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = 1)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .rax → r' ≠ .rdx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .rdx = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt hcx hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.rdx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [hax, Nat.pow_zero, Nat.mul_one], by rw [hdx]; rfl⟩

end VG.Proof.Scrypt.X86_64.RoMix
