import VerifiedGarbage.Proof.Scrypt.X86.RoMix

/-!
# scryptROMix on x86 (32-bit): the small loops

The word copy (`copyLoop`), the word exclusive-or (`xorLoop`) and the
computation of `2 N` by doubling (`nLoop`), as on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`). Words are 4 bytes, and pointers 32 bits,
which address memory by their zero extensions.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_cmp
  ofNat_beq_zero sub_beq)

/-! ## Arithmetic -/

/-- A pointer advanced by one word. -/
theorem next32 (p : BitVec 32) (k : Nat) :
    p + BitVec.ofNat 32 (4 * k) + 4 = p + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [add32_lit, Nat.mul_succ]

theorem ofNat_zero_add32 (p : BitVec 32) : p + BitVec.ofNat 32 (4 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-- A word of a region, as an address. -/
theorem word_addr {p : BitVec 32} {n k : Nat} (hp : p.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    addr (p + BitVec.ofNat 32 (4 * k)) 0 = p.setWidth 64 + BitVec.ofNat 64 (4 * k) := by
  rw [addr_zero, addr_add (by omega)]

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  eax : t.gpr .eax = src + BitVec.ofNat 32 (4 * k)
  ecx : t.gpr .ecx = dst + BitVec.ofNat 32 (4 * k)
  edx : t.gpr .edx = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (4 * k))

theorem copy_step {s : State} {src dst : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 4 * n⟩ ⟨dst.setWidth 64, 4 * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : CopyInv s src dst n k t) :
    WP isa (.block [.mov .edi (.mem (at_ .eax 0)), .store (at_ .ecx 0) .edi, .alu .add .eax (.imm 4),
      .alu .add .ecx (.imm 4), .alu .sub .edx (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := src.setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, h.eax, word_addr fs hk]) (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store (a := dst.setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, u₁.other _ (by decide), h.ecx, word_addr fd hk])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ u₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .edi → t₂.gpr r = t.gpr r := fun r hr => by rw [u₂.gpr, u₁.other r hr]
  have e2 : t₄.gpr .edx = BitVec.ofNat 32 (n - k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.edx]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], fun r h0 h1 h2 h3 => ?_, ?_, ?_,
    by rw [u₅.gpr, e2, dec_count hk], ?_⟩, by rw [z₅, e2, dec_z hk hn]⟩
  · rw [u₅.other r h2, u₄.other r h1, u₃.other r h0, g r h3, h.other r h0 h1 h2 h3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.eax, next32]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.ecx, next32]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact Proof.Scrypt.Memory.copy_mem s.mem _ _ k 4
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)

/-- `copyLoop` copies `4 n` bytes from `eax` to `ecx` (`edx = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fs : src.toNat + 4 * n ≤ 2 ^ 32) (fd : dst.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = src) (h1 : s.gpr .ecx = dst) (h2 : s.gpr .edx = BitVec.ofNat 32 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 4 * n⟩ ⟨dst.setWidth 64, 4 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (4 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt fs fd hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [h2, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → t.gpr r = s.gpr r
  eax : t.gpr .eax = x + BitVec.ofNat 32 (4 * k)
  ecx : t.gpr .ecx = y + BitVec.ofNat 32 (4 * k)
  edx : t.gpr .edx = d + BitVec.ofNat 32 (4 * k)
  edi : t.gpr .edi = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (d.setWidth 64)
    (xorBytes (bytesAt s.mem (x.setWidth 64) (4 * k)) (bytesAt s.mem (y.setWidth 64) (4 * k)))

theorem xor_step {s : State} {x y d : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 4 * n⟩ ⟨x.setWidth 64, 4 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 4 * n⟩ ⟨y.setWidth 64, 4 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.mov .esi (.mem (at_ .eax 0)), .alu .xor .esi (.mem (at_ .ecx 0)),
      .store (at_ .edx 0) .esi, .alu .add .eax (.imm 4), .alu .add .ecx (.imm 4), .alu .add .edx (.imm 4),
      .alu .sub .edi (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := x.setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, h.eax, word_addr fx hk]) (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_xorm (a := y.setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, u₁.other _ (by decide), h.ecx, word_addr fy hk])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_store (a := d.setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.edx, word_addr fd hk])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₃ u₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ => wp_subi fun t₇ u₇ z₇ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .esi → t₃.gpr r = t.gpr r := fun r hr => by
    rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  have e7 : t₆.gpr .edi = BitVec.ofNat 32 (n - k) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g _ (by decide), h.edi]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h0 h1 h2 h3 h4 => ?_, ?_, ?_, ?_, by rw [u₇.gpr, e7, dec_count hk], ?_⟩,
    by rw [z₇, e7, dec_z hk hn]⟩
  · rw [u₇.other r h3, u₆.other r h2, u₅.other r h1, u₄.other r h0, g r h4,
      h.other r h0 h1 h2 h3 h4]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g _ (by decide), h.eax, next32]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g _ (by decide), h.ecx, next32]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.edx, next32]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem4 s.mem hk (by omega) hdx hdy

/-- `xorLoop` writes `[eax] xor [ecx]` to `edx`, `4 n` bytes (`edi = n > 0` words). -/
theorem xorLoop_ok {s : State} {x y d : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fx : x.toNat + 4 * n ≤ 2 ^ 32) (fy : y.toNat + 4 * n ≤ 2 ^ 32) (fd : d.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = x) (h1 : s.gpr .ecx = y) (h2 : s.gpr .edx = d)
    (h3 : s.gpr .edi = BitVec.ofNat 32 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 4 * n⟩ ⟨x.setWidth 64, 4 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 4 * n⟩ ⟨y.setWidth 64, 4 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (4 * n)) (bytesAt s.mem (y.setWidth 64) (4 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt fx fy fd hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add32, h0],
    by rw [ofNat_zero_add32, h1], by rw [ofNat_zero_add32, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .eax → r' ≠ .ecx → t.gpr r' = s.gpr r'
  eax : t.gpr .eax = BitVec.ofNat 32 (r * 2 ^ k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (2 ^ k)

theorem dbl_pow32 (x k : Nat) : BitVec.ofNat 32 (x * 2 ^ k) + BitVec.ofNat 32 (x * 2 ^ k) =
    BitVec.ofNat 32 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .ecx (.reg .ecx), .alu .cmp .eax (.reg .edx)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ f₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .eax = BitVec.ofNat 32 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.eax, dbl_pow32]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [f₃.mem, u₂.mem, u₁.mem, h.mem], fun r' h0 h1 => ?_, by rw [f₃.gpr, ax], ?_⟩, ?_⟩
  · rw [f₃.gpr, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1]
  · rw [f₃.gpr, u₂.gpr, u₁.other _ (by decide), h.ecx, ← Nat.one_mul (2 ^ k), dbl_pow32, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), h2, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, hh]

/-- `nLoop` doubles `eax` (from `r`) and `ecx` (from 1) until `eax = edx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h0 : s.gpr .eax = BitVec.ofNat 32 r) (h1 : s.gpr .ecx = 1)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ecx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .ecx = BitVec.ofNat 32 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.ecx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.X86.RoMix
