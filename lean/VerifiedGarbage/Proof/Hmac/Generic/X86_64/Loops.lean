import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Spec.Pbkdf2
import Mathlib.Tactic.Set

/-!
# HMAC over any streaming hash function on x86-64: the byte loops

Untrusted: everything here is checked by Lean. The byte copy (`copy`), used
for states, digests and `U`; the exclusive-or of `U` into `T`; and `init`'s
loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts `r14` up from 0
and ends when it reaches its bound.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash byteAt copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeW8_apply)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32i wp_addi wp_cmp wp_cmpi wp_movzx8 wp_store8
  ofNat_succ sub_beq)
open VG.Proof.Hmac.X86_64 (bytesAt_add bytesAt_length)
open Spec.Sha256 (bytesAt)

/-! ## Arithmetic -/

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega)]
  exact zx_ofNat (by omega)

theorem sx_one : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem ea_byteAt (s : State) (b : Reg) (o k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea (byteAt b o) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  simp only [State.ea, byteAt, h14, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-- A byte written is a one-byte `writeBytes`. -/
theorem writeW_byte (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  rw [writeW8_apply]
  simp only [writeBytes, List.length_singleton]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 1 := fun h' => h (by
      have : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by simpa using this)
      bv_omega)
    simp only [h, this, ↓reduceIte]

/-- One more byte written after `k`. -/
theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (hl : xs.length + 1 < 2 ^ 64) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b = writeBytes m q (xs ++ [b]) := by
  rw [writeW_byte, writeBytes_append _ _ _ _ (by simpa using hl)]

theorem bytesAt_snoc' (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add]; simp [bytesAt]

/-- Every byte of a sub-region of a region in `rs` is in `rs`. -/
theorem inRegions_of_sub {rs : List Region} {R : Region} (hR : R ∈ rs) {p : Addr} {n : Nat}
    (hs : Region.Sub ⟨p, n⟩ R) (hn : n < 2 ^ 64) {k : Nat} (hk : k < n) :
    InRegions rs (p + BitVec.ofNat 64 k) 1 :=
  ⟨R, hR, hs _ (Proof.Sha256.X86_64.contains_offset (by omega) (by omega))⟩

/-- A byte of `⟨p, n⟩` is not among the first `k ≤ n` of a disjoint region. -/
theorem not_mem_of_disjoint {p q : Addr} {n k j : Nat} (hd : Region.Disjoint ⟨p, n⟩ ⟨q, n⟩) (hj : j < n)
    (hk : k ≤ n) (hn : n < 2 ^ 64) : ¬ ((p + BitVec.ofNat 64 j) - q).toNat < k := fun h =>
  hd _ (Proof.Sha256.X86_64.contains_offset (base := p) (len := n) (off := j) (n := 1)
    (by omega) (by omega)) (by
    show ((p + BitVec.ofNat 64 j) - q).toNat + 1 ≤ n; omega)

theorem InRegions.right' {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

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

/-- `r14` counted up to `n`: the flags after `add r14, 1; cmp r14, n`. -/
theorem count_zf {k n : Nat} (hk : k < n) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 - (BitVec.ofNat 32 n).signExtend 64 == 0) =
      decide (k + 1 = n) := by
  rw [sx_one, sx_ofNat hn, ← ofNat_succ, sub_beq (by omega) (by omega)]

/-! ## `copy` -/

/-- After `k` bytes of `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ≠ .rax ∧ src ≠ .r14) (hd : dst ≠ .rax ∧ dst ≠ .r14)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 so, n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s (s.gpr dst + BitVec.ofNat 64 d) (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) n) t := by
  set A := s.gpr src + BitVec.ofNat 64 so
  set B := s.gpr dst + BitVec.ofNat 64 d
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k) (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ hs.1 hs.2])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ hd.1,
      h.other _ hd.1 hd.2]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14, sx_one, ← ofNat_succ], ?_⟩, by rw [z₄, h14, count_zf hk hn']⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, bytesAt_snoc']
  have e : writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (le_of_lt hk) (by omega), ↓reduceIte]
  have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']

/-! ## Addresses -/

theorem add_ofNat_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := fun e =>
  h (by
    have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
    rwa [toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this)

theorem add_ofNat_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The exclusive-or of `U` into `T` -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ v).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.imm v) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem xor_byte2 (a b : Byte) :
    ((((a.setWidth 64).setWidth 32 ^^^ (b.setWidth 64).setWidth 32).setWidth 64).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor, Bool.xor_comm]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

theorem xorBytes_snoc (a b : List Byte) (x y : Byte) (h : a.length = b.length) :
    Spec.Pbkdf2.xorBytes (a ++ [x]) (b ++ [y]) = Spec.Pbkdf2.xorBytes a b ++ [x ^^^ y] := by
  simp [Spec.Pbkdf2.xorBytes, List.zipWith_append h]

theorem xorBytes_length' (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `r15 + uo` and `T` at `r12`. -/
theorem xor_ok {uo n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 0 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r15 + BitVec.ofNat 64 uo, n⟩ ⟨s.gpr .r12, n⟩) :
    WP isa (.seq (.block [.mov32 .r14 (.imm 0)])
      (.loop (.block [.movzx8 .rax (byteAt .r15 uo), .movzx8 .rcx (byteAt .r12 0),
        .alu32 .xor .rax (.reg .rcx), .store8 (byteAt .r12 0) .rax, .alu .add .r14 (.imm 1),
        .alu .cmp .r14 (.imm (BitVec.ofNat 32 n))]) .ne)) s
      fun t => XorInv s (s.gpr .r15 + BitVec.ofNat 64 uo) (s.gpr .r12) n t := by
  set U := s.gpr .r15 + BitVec.ofNat 64 uo
  set T := s.gpr .r12
  have hT0 : T + BitVec.ofNat 64 0 = T := BitVec.add_zero _
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (le_of_lt hk) (by omega), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by bv_omega,
      toNat_ofNat_lt (show k < 2 ^ 64 by omega), Nat.lt_irrefl, ↓reduceIte]
  refine wp_movzx8 (a := U + BitVec.ofNat 64 k) (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide)])
    (by rw [h.rd, h.wr]; exact hinU k hk) fun t₁ u₁ => ?_
  refine wp_movzx8 (a := T + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ (by decide),
      h.other _ (by decide) (by decide) (by decide), hT0])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact InRegions.right' (hT0 ▸ houtT k hk)) fun t₂ u₂ => ?_
  refine wp_xor32r fun t₃ u₃ => ?_
  refine wp_store8 (a := T + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14]), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide), hT0])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hT0 ▸ houtT k hk) fun t₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_cmpi fun t₆ g₆ m₆ rd₆ wr₆ _ z₆ => WP.block_nil ?_
  have h14 : t₅.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₅.gpr, g₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r ha hc h14' => by
      rw [g₆, u₅.other r h14', g₄, u₃.other r ha, u₂.other r hc, u₁.other r ha, h.other r ha hc h14'],
    by rw [g₆, h14, sx_one, ← ofNat_succ], ?_⟩, by rw [z₆, h14, count_zf hk hn']⟩
  have hv : (t₃.gpr .rax).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, xor_byte2, u₁.mem, rU, rT]
  have e' := writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
    (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega)
  rw [hl'] at e'
  rw [m₆, u₅.mem, m₄, hv, u₃.mem, u₂.mem, u₁.mem, h.mem, e', bytesAt_snoc', bytesAt_snoc',
    xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P` and `K₀ ⊕ opad` at `P + B`, byte by byte: first
the key's `kl` bytes (read at `K`), then the zeros that pad it to `B`. -/

section
variable (B : Nat) (P K : Addr) (K0 : List Byte) (m₀ : Mem)

/-- `j` bytes of each block written, and nothing else. -/
structure BufMem (j : Nat) (m : Mem) : Prop where
  bufI : bytesAt m P j = (K0.take j).map (· ^^^ Spec.Hmac.ipad)
  bufO : bytesAt m (P + BitVec.ofNat 64 B) j = (K0.take j).map (· ^^^ Spec.Hmac.opad)
  frame : Frame [⟨P, 2 * B⟩] m₀ m

end

theorem bytesAt_prefix_congr {m m' : Mem} {p : Addr} {j : Nat} (h : ∀ i < j, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' p j = bytesAt m p j := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem buf_write {B : Nat} {P : Addr} {K0 : List Byte} {m₀ : Mem} {j : Nat} {m : Mem}
    (h : BufMem B P K0 m₀ j m) (hB : B ≤ 128) (hj : j < B) (hl : j < K0.length) :
    BufMem B P K0 m₀ (j + 1) ((m.writeW (P + BitVec.ofNat 64 j) (K0[j] ^^^ Spec.Hmac.ipad)).writeW
      (P + BitVec.ofNat 64 B + BitVec.ofNat 64 j) (K0[j] ^^^ Spec.Hmac.opad)) := by
  have neI : ∀ i < B, P + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 B + BitVec.ofNat 64 j := fun i hi => by
    rw [add_ofNat_add]; exact add_ofNat_ne _ (by omega) (by omega) (by omega)
  have neO : ∀ i < j, P + BitVec.ofNat 64 B + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 j := fun i hi => by
    rw [add_ofNat_add]; exact add_ofNat_ne _ (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [bytesAt_snoc', List.take_succ_eq_append_getElem hl, List.map_append, ← h.bufI]
    congr 1
    · refine bytesAt_prefix_congr fun i hi => ?_
      simp only [writeW8_apply, neI i (by omega),
        add_ofNat_ne P (a := i) (b := j) (by omega) (by omega) (by omega), ↓reduceIte]
    · simp only [writeW8_apply, neI j hj, ↓reduceIte, List.map_cons, List.map_nil]
  · rw [bytesAt_snoc', List.take_succ_eq_append_getElem hl, List.map_append, ← h.bufO]
    congr 1
    · refine bytesAt_prefix_congr fun i hi => ?_
      have e1 : P + BitVec.ofNat 64 B + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 B + BitVec.ofNat 64 j := by
        rw [add_ofNat_add, add_ofNat_add]; exact add_ofNat_ne _ (by omega) (by omega) (by omega)
      simp only [writeW8_apply, e1, neO i hi, ↓reduceIte]
    · simp only [writeW8_apply, ↓reduceIte, List.map_cons, List.map_nil]
  · refine (h.frame.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · exact Proof.Sha256.X86_64.contains_offset (by omega) (by omega)
    · rw [add_ofNat_add]; exact Proof.Sha256.X86_64.contains_offset (by omega) (by omega)

variable (H : Hash)

/-- Where the loops are. -/
structure LoopRegs (P K : Addr) (kl : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 + BitVec.ofNat 64 H.buf = P
  rbp : s.gpr .rbp = K
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl

theorem LoopRegs.keep {P K : Addr} {kl : Nat} {s t : State} (h : LoopRegs H P K kl s)
    (hk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r) : LoopRegs H P K kl t :=
  ⟨by rw [hk _ (by decide) (by decide) (by decide), h.r15], by rw [hk _ (by decide) (by decide) (by decide), h.rbp],
    by rw [hk _ (by decide) (by decide) (by decide), h.r13]⟩

/-- The key: its `kl` bytes at `K`, then zeros up to `B`. -/
def K0 (m : Mem) (K : Addr) (kl B : Nat) : List Byte := bytesAt m K kl ++ List.replicate (B - kl) 0

theorem K0_length (m : Mem) (K : Addr) {kl B : Nat} (h : kl ≤ B) : (K0 m K kl B).length = B := by
  simp [K0, bytesAt_length]; omega

theorem K0_lt {m : Mem} {K : Addr} {kl B j : Nat} (hj : j < kl) (h : j < (K0 m K kl B).length) :
    (K0 m K kl B)[j] = m (K + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {m : Mem} {K : Addr} {kl B j : Nat} (hj : kl ≤ j) (h : j < (K0 m K kl B).length) :
    (K0 m K kl B)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

/-- The loops' invariant, from the state `s` they start in. -/
structure KeyInv (s : State) (P K : Addr) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : BufMem H.B P (K0 s.mem K kl H.B) s.mem j t.mem

theorem xor_byte (b : Byte) (v : BitVec 32) :
    ((((b.setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem xor_byte' (b : Byte) (v : BitVec 32) :
    ((((((b.setWidth 64).setWidth 32).setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 =
      b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-- The regions the loops access. -/
structure LoopMem (P K : Addr) (kl : Nat) (s : State) : Prop where
  kl_le : kl ≤ H.B
  key : ∀ k < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  buf : ∀ k < 2 * H.B, InRegions s.wr (P + BitVec.ofNat 64 k) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, 2 * H.B⟩
  hB : H.B ≤ 128

theorem key_step {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    {j : Nat} (hj : j < kl) {t : State} (h : KeyInv H s P K kl j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .mov32 .rcx (.reg .rax),
      .alu32 .xor .rax (.imm 0x36), .store8 (byteAt .r15 H.buf) .rax, .alu32 .xor .rcx (.imm 0x5c),
      .store8 (byteAt .r15 (H.buf + H.B)) .rcx, .alu .add .r14 (.imm 1),
      .alu .cmp .r14 (.reg .r13)]) t fun t' => KeyInv H s P K kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.Sha256.X86_64.contains_offset (n := 1) (by omega) (by omega)) hc
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j) (by rw [ea_byteAt _ _ _ _ h.r14, rt.rbp, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hm.key j hj) fun t₁ u₁ => ?_
  refine wp_mov32r fun t₂ u₂ => wp_xor32i fun t₃ u₃ => ?_
  have e14 : ∀ t' : State, t'.gpr .r14 = t.gpr .r14 → t'.gpr .r15 = t.gpr .r15 → ∀ o,
      t'.ea (byteAt .r15 o) = t.gpr .r15 + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun t' a b o => by
    rw [ea_byteAt _ _ _ j (by rw [a, h.r14]), b]
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [e14 _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]), rt.r15])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_xor32i fun t₅ u₅ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [e14 _ (by rw [u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]) (by rw [u₅.other _ (by decide), g₄, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]), ← add_ofNat_add, rt.r15])
    (by rw [u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega))
    fun t₆ g₆ m₆ rd₆ wr₆ => ?_
  refine wp_addi fun t₇ u₇ => wp_cmp fun t₈ g₈ m₈ rd₈ wr₈ _ z₈ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t₈.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [g₈, u₇.other r h3, g₆, u₅.other r h2, g₄, u₃.other r h1, u₂.other r h2, u₁.other r h1]
  have h14 : t₇.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₇.gpr, g₆, u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₈, u₇.rd, rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [wr₈, u₇.wr, wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 => by rw [k r h1 h2 h3, h.other r h1 h2 h3], by rw [g₈, h14], ?_⟩, ?_⟩
  · have v₁ : (t₃.gpr .rax).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
      rw [u₃.gpr, u₂.other .rax (by decide), u₁.gpr, xor_byte, hbyte]; rfl
    have v₂ : (t₅.gpr .rcx).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
      rw [u₅.gpr, g₄, u₃.other .rcx (by decide), u₂.gpr, u₁.gpr, xor_byte', hbyte]; rfl
    rw [m₈, u₇.mem, m₆, v₂, u₅.mem, m₄, v₁, u₃.mem, u₂.mem, u₁.mem]
    exact buf_write h.mem hB (by omega) hl
  · rw [z₈, h14, show t₇.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₇.other _ (by decide), g₆, u₅.other _ (by decide), g₄, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), rt.r13], sub_beq (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) H.keyLoop) s (KeyInv H s P K kl kl) := by
  have i0 : KeyInv H s P K kl 0 s :=
    ⟨rfl, rfl, fun _ _ _ _ => rfl, h14, ⟨by simp [bytesAt], by simp [bytesAt], Frame.refl _ _⟩⟩
  refine WP.ite (decide (kl = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (KeyInv H s P K kl) (fun j hj t h => key_step H hr hm hj h) i0

/-- In the pad loop, `rax` and `rcx` hold `ipad` and `opad`. -/
structure PadInv (s₀ : State) (P K : Addr) (kl j : Nat) (t : State) : Prop extends
    KeyInv H s₀ P K kl j t where
  rax : t.gpr .rax = (0x36 : BitVec 32).setWidth 64
  rcx : t.gpr .rcx = (0x5c : BitVec 32).setWidth 64

theorem pad_step {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State} (h : PadInv H s₀ P K kl j t) :
    WP isa (.block [.store8 (byteAt .r15 H.buf) .rax, .store8 (byteAt .r15 (H.buf + H.B)) .rcx,
      .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))]) t
      fun t' => PadInv H s₀ P K kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = H.B)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (by rw [ea_byteAt _ _ _ _ h.r14, rt.r15])
    (by rw [h.wr]; exact hm.buf j (by omega)) fun t₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ j (by rw [g₁, h.r14]), g₁, ← add_ofNat_add, rt.r15])
    (by rw [wr₁, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega)) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r14 → t₄.gpr r = t.gpr r := fun r h1 => by rw [g₄, u₃.other r h1, g₂, g₁]
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 j + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, g₁, h.r14]
  refine ⟨⟨⟨by rw [rd₄, u₃.rd, rd₂, rd₁, h.rd], by rw [wr₄, u₃.wr, wr₂, wr₁, h.wr],
    fun r h1 h2 h3 => by rw [k r h3, h.other r h1 h2 h3], by rw [g₄, h14, sx_one, ← ofNat_succ], ?_⟩,
    by rw [k _ (by decide), h.rax], by rw [k _ (by decide), h.rcx]⟩, ?_⟩
  · have e : ∀ v : BitVec 32, ((v.setWidth 64).setWidth 8) = (0 : Byte) ^^^ v.setWidth 8 := fun v => by
      ext i hi; simp [BitVec.getElem_setWidth]
    rw [m₄, u₃.mem, m₂, m₁, g₁, h.rax, h.rcx, e, e, ← K0_ge (m := s₀.mem) (K := K) (B := H.B) hj hl]
    exact buf_write h.mem hB hj' hl
  · rw [z₄, h14, count_zf hj' (by omega)]

/-- The pad loop, skipped for a key of `B` bytes. -/
theorem pad_ok {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {t : State} (h : KeyInv H s₀ P K kl kl t) :
    WP isa (.seq (.block [.mov32 .rax (.imm 0x36), .mov32 .rcx (.imm 0x5c),
        .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))]) (.ite .e (.block []) H.padLoop)) t
      (KeyInv H s₀ P K kl H.B) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  refine WP.seq (wp_mov32i fun t₁ u₁ _ _ => wp_mov32i fun t₂ u₂ _ _ =>
    wp_cmpi fun t₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_)
  have i0 : PadInv H s₀ P K kl kl t₃ :=
    ⟨⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
      fun r h1 h2 h3 => by rw [g₃, u₂.other r h2, u₁.other r h1, h.other r h1 h2 h3],
      by rw [g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14],
      by rw [m₃, u₂.mem, u₁.mem]; exact h.mem⟩,
      by rw [g₃, u₂.other _ (by decide), u₁.gpr], by rw [g₃, u₂.gpr]⟩
  have hz : t₃.zf = some (decide (kl = H.B)) := by
    rw [z₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, sx_ofNat (by omega),
      sub_beq (by omega) (by omega)]
  refine WP.ite (decide (kl = H.B)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0.toKeyInv
  · have : kl < H.B := by simp at h0; omega
    refine WP.mono (WP.loop (M := isa) (fun n t => ∃ j, n = H.B - j ∧ kl ≤ j ∧ j < H.B ∧ PadInv H s₀ P K kl j t)
      ?_ (H.B - kl) t₃ ⟨kl, rfl, (Nat.le_refl _), this, i0⟩) fun _ h => h
    rintro n t ⟨j, rfl, hj, hj', hb⟩
    refine WP.mono (pad_step H hr hm hj hj' hb) fun t' ⟨hb', hz'⟩ => ?_
    by_cases hl : j + 1 = H.B
    · exact .inl ⟨by simp [eval, hz', hl], hl ▸ hb'.toKeyInv⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

end VG.Proof.Hmac.Generic.X86_64
