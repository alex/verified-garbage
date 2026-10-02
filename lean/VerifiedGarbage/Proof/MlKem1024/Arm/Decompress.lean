import VerifiedGarbage.Proof.MlKem.Arm.Decompress
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Impl.MlKem1024.Arm.Poly
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_decode_decompress`

A loop for each width `d ∈ {5, 11}` over the 32 groups of `d` bytes, whose
body is the 8 fields of a group, each run once for any field (`field_step`)
from the steps of its code: the first byte of the field shifted down
(`head_ok`), each next byte shifted up and added (`next_ok`, composed by
`loads_ok`), the reduction modulo `2ᵈ` (`mask_ok`) and `Decompress_d` stored
(`store_ok`). The value of the field is `bsum` of its bytes, shifted down;
that it is field `e` of `ByteDecode_d` is `decodeDecompress5_0` …
`decodeDecompress11_7`, one `omega` for each (`fieldVal5`, `fieldVal11`).
-/

namespace VG.Proof.MlKem1024.Arm.Decompress

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm
open VG.Proof.MlKem.Arm.Add (ptr_succ)
open VG.Proof.MlKem.Arm.Decompress (dec)

/-! ## The values -/

theorem mem_widths {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

theorem dec_toNat4 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : BitVec 32} (hy : y.toNat < 2 ^ d) :
    (dec d y).toNat = (decompress d y.toNat).val := by
  rw [(decompress1024_val hd hy).1]
  unfold dec
  rw [q_eq]
  rcases mem_widths hd with rfl | rfl <;> bv_omega

/-- A decompressed field, as a stored word. -/
theorem dec_eq4 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : BitVec 32} {n : Nat} (hy : y.toNat = n)
    (hn : n < 2 ^ d) : dec d y = BitVec.ofNat 32 (decompress d n).val :=
  ofNat_val_eq (by rw [dec_toNat4 hd (hy ▸ hn), hy])

/-- The `n` bytes `g j, …, g (j + n - 1)`, as a little-endian number. -/
def bsum (g : Nat → Byte) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum g j n + (g (j + n)).toNat * 256 ^ n

theorem bsum_lt (g : Nat → Byte) (j : Nat) : ∀ n, bsum g j n < 256 ^ n
  | 0 => by simp [bsum]
  | n + 1 => by
    have := bsum_lt g j n
    have hb := (g (j + n)).isLt
    have : (g (j + n)).toNat * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    rw [bsum, Nat.pow_succ]
    omega

/-- A byte shifted up by `8m - t` and added to a number of `m` bytes
shifted down by `t`. -/
theorem shift_step {A t m : Nat} (b : Byte) (ht : t < 8) (hm : m = 1 ∨ m = 2) (hA : A < 256 ^ m) :
    BitVec.ofNat 32 (A / 2 ^ t) + (b.setWidth 32 <<< (8 * m - t)) =
      BitVec.ofNat 32 ((A + b.toNat * 256 ^ m) / 2 ^ t) := by
  have hb := b.isLt
  rcases hm with rfl | rfl <;>
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.pow_one] at hA ⊢ <;> bv_omega

/-- Reduced modulo `2ᵈ` by a pair of shifts. -/
theorem mask_eq {d V : Nat} (hd : d = 5 ∨ d = 11) (hV : V < 2 ^ 32) :
    (BitVec.ofNat 32 V <<< (32 - d)) >>> (32 - d) = BitVec.ofNat 32 (V % 2 ^ d) := by
  rcases hd with rfl | rfl <;> bv_omega

/-! ## The steps of a field -/

/-- What the loads of a field keep. -/
structure Keeps (s s' : State) : Prop where
  r0 : s'.gpr .r0 = s.gpr .r0
  r1 : s'.gpr .r1 = s.gpr .r1
  r3 : s'.gpr .r3 = s.gpr .r3
  pres : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.r0.trans h₁.r0, h₂.r1.trans h₁.r1, h₂.r3.trans h₁.r3, fun r hr => (h₂.pres r hr).trans (h₁.pres r hr),
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

section
variable {s : State} {x : BitVec 32}

theorem head_ok {j t : Nat} (hj : j < 4096) (ht : t < 8) (h0 : s.gpr .r0 = x)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 j)) 1) :
    WP isa (.block (ddHead j t)) s fun s' =>
      Keeps s s' ∧ s'.gpr .r2 = BitVec.ofNat 32 ((s.mem (State.addr (x + BitVec.ofNat 32 j))).toNat / 2 ^ t) := by
  unfold ddHead
  by_cases h : t = 0
  · subst h
    simp only [↓reduceIte]
    run_block [h0, i0, hj]
    refine ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl, rfl⟩, ?_⟩
    rw [Nat.pow_zero, Nat.div_one]
    apply BitVec.eq_of_toNat_eq
    rw [setWidth32_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := (s.mem (State.addr (x + BitVec.ofNat 32 j))).isLt; omega)]
  · simp only [h, ↓reduceIte]
    have hsh : 1 ≤ t ∧ t ≤ 31 := by omega
    run_block [h0, i0, hj, hsh]
    refine ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl, rfl⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (State.addr (x + BitVec.ofNat 32 j))).isLt
    rw [BitVec.toNat_ushiftRight, setWidth32_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]

theorem next_ok {j t i : Nat} (hj : j + 1 + i < 4096) (hsh : 1 ≤ 8 * (i + 1) - t ∧ 8 * (i + 1) - t ≤ 31)
    (h0 : s.gpr .r0 = x) (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (j + 1 + i))) 1) :
    WP isa (.block (ddNext j t i)) s fun s' =>
      Keeps s s' ∧ s'.gpr .r2 = s.gpr .r2 +
        ((s.mem (State.addr (x + BitVec.ofNat 32 (j + 1 + i)))).setWidth 32 <<< (8 * (i + 1) - t)) := by
  run_block [ddNext, h0, i1, hj, hsh]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl, rfl⟩, trivial⟩

end

/-- The loads of a field of `n ≤ 3` bytes from byte `j`, starting at bit `t`:
`r2` is their number, shifted down by `t`. -/
theorem loads_ok {s : State} {x : BitVec 32} {g : Nat → Byte} {j t n : Nat} (hj : j + n < 4096) (ht : t < 8)
    (hn : 1 ≤ n ∧ n ≤ 3) (h0 : s.gpr .r0 = x)
    (ib : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (j + k))) 1)
    (hg : ∀ k < n, s.mem (State.addr (x + BitVec.ofNat 32 (j + k))) = g (j + k)) :
    WP isa (.block (ddHead j t ++ (List.range (n - 1)).flatMap (ddNext j t))) s fun s' =>
      Keeps s s' ∧ s'.gpr .r2 = BitVec.ofNat 32 (bsum g j n / 2 ^ t) := by
  rw [WP.block_append_iff]
  have i0 := ib 0 (by omega)
  have g0 := hg 0 (by omega)
  rw [Nat.add_zero] at i0 g0
  refine WP.mono (head_ok (by omega) ht h0 i0) fun s₁ ⟨k₁, v₁⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (f := ddNext j t) (N := n - 1)
    (fun i s' => Keeps s s' ∧ s'.gpr .r2 = BitVec.ofNat 32 (bsum g j (i + 1) / 2 ^ t))
    (fun i s' hi ⟨k', v'⟩ => ?_) (n - 1) (Nat.le_refl _) s₁ ⟨k₁, ?_⟩) fun s' h => ?_
  · have i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (j + 1 + i))) 1 := by
      rw [show j + 1 + i = j + (i + 1) by omega]; exact ib (i + 1) (by omega)
    have g1 : s.mem (State.addr (x + BitVec.ofNat 32 (j + 1 + i))) = g (j + (i + 1)) := by
      rw [show j + 1 + i = j + (i + 1) by omega]; exact hg (i + 1) (by omega)
    refine WP.mono (next_ok (by omega) (by omega) (k'.r0.trans h0) (by rw [k'.rd, k'.wr]; exact i1))
      fun s₂ ⟨k₂, v₂⟩ => ⟨k'.trans k₂, ?_⟩
    rw [v₂, k'.mem, g1, v', shift_step _ ht (by omega) (bsum_lt g j (i + 1))]
    rfl
  · rw [v₁, g0]; simp [bsum]
  · have e : n - 1 + 1 = n := by omega
    rw [e] at h; exact h

theorem mask_ok {s : State} {d V : Nat} (hd : d = 5 ∨ d = 11) (hV : V < 2 ^ 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 V) :
    WP isa (.block ([.mov .r2 (.shifted .r2 .lsl (32 - d)), .mov .r2 (.shifted .r2 .lsr (32 - d))] :
      List Instr)) s fun s' => Keeps s s' ∧ s'.gpr .r2 = BitVec.ofNat 32 (V % 2 ^ d) := by
  have hsh : 1 ≤ 32 - d ∧ 32 - d ≤ 31 := by omega
  run_block [h2, hsh]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl, rfl⟩, mask_eq hd hV⟩

theorem store_ok {s : State} {d off : Nat} {y a : BitVec 32} (he : encodable (BitVec.ofNat 32 (2 ^ (d - 1))) = true)
    (hsh : 1 ≤ d ∧ d ≤ 31) (hoff : off < 4096) (h2 : s.gpr .r2 = y) (h3 : s.gpr .r3 = a)
    (o : InRegions s.wr (State.addr (a + BitVec.ofNat 32 off)) 4) :
    WP isa (.block (decompressTo d off)) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (State.addr (a + BitVec.ofNat 32 off)) (dec d y) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [decompressTo, dec, he, hsh, hoff, h2, h3, o, preserved, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_self, and_true]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pb : BitVec 32 := s₀.gpr .r0
abbrev len : Nat := (s₀.gpr .r1).toNat
abbrev dd : Nat := (s₀.gpr .r2).toNat
abbrev pf : BitVec 32 := s₀.gpr .r3
abbrev B : Addr := State.addr (pb s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev inR : Region := ⟨B s₀, len s₀⟩
abbrev bs : List Byte := bytesAt s₀.mem (B s₀) (len s₀)
abbrev D : Poly := decodeDecompress (dd s₀) (bs s₀)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (pb s₀).toNat + len s₀ ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  d : dd s₀ ∈ Spec.MlKem1024.compressWidths
  len : len s₀ = 32 * dd s₀

/-- Within iteration `i` of the loop, after the first `e` fields of the group. -/
structure Mid (s₀ : State) (i e : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (dd s₀ * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (dd s₀ * (32 - i))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 8 * i + e then out s₀ j else coeffAt s₀.mem (F s₀) j

section
variable {s₀ : State} (hp : Pre s₀) {S T K i : Nat} {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
  (hf : Frame [polyRegion (F s₀)] s₀.mem s.mem)
include hp hrd hwr hf

/-- Byte `S i + k` of the input: its address, that it can be read, and its value. -/
theorem byte_at {k : Nat} (hk : S * i + k < len s₀) :
    State.addr (pb s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 k) = B s₀ + BitVec.ofNat 64 (S * i + k) ∧
    InRegions (s.rd ++ s.wr) (B s₀ + BitVec.ofNat 64 (S * i + k)) 1 ∧
    s.mem (B s₀ + BitVec.ofNat 64 (S * i + k)) = (bs s₀).getD (S * i + k) 0 ∧
    (inR s₀).Contains (B s₀ + BitVec.ofNat 64 (S * i + k)) 1 := by
  have fB := hp.fitB
  have c : (inR s₀).Contains (B s₀ + BitVec.ofNat 64 (S * i + k)) 1 := contains_off (by omega) (by omega)
  refine ⟨addr_byte fB rfl hk, ?_, ?_, c⟩
  · rw [hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) c
  · rw [bytesAt_getD _ _ hk]
    exact frame_byte hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by omega) hk

omit hrd hf in
/-- Coefficient `K i + k` of the output: its address, and that it can be written. -/
theorem coeff_at (hT : T = 4 * K) {k : Nat} (hk : K * i + k < 256) :
    State.addr (pf s₀ + BitVec.ofNat 32 (T * i) + BitVec.ofNat 32 (4 * k)) = coeffAddr (F s₀) (K * i + k) ∧
    InRegions s.wr (coeffAddr (F s₀) (K * i + k)) 4 ∧
    (polyRegion (F s₀)).Contains (coeffAddr (F s₀) (K * i + k)) 4 := by
  have fF := hp.fitF
  have c := coeff_contains (F s₀) (i := K * i + k) (by rw [n_eq]; omega)
  refine ⟨addr_coeff fF (by subst hT; rw [Nat.mul_assoc, ← Nat.mul_add]) (by omega), ?_, c⟩
  rw [hwr, hp.wr]; exact inRegions_of (by simp) c

end

/-! ## The fields -/

/-- The fields of a group of `d` bytes: within the group, of at most three
bytes, starting at a bit of a byte. -/
theorem fields_ok : ∀ d ∈ [5, 11], ∀ e < 8,
    (fieldAt d e).1 + (fieldAt d e).2.2 ≤ d ∧ (fieldAt d e).2.1 < 8 ∧ 1 ≤ (fieldAt d e).2.2 ∧
      (fieldAt d e).2.2 ≤ 3 := by
  decide

section
variable (g : Nat → Byte)

/-- Field `e` of `ByteDecode₅`, from its bytes. -/
theorem fieldVal5 {B : List Byte} (hB : B.length = 160) {i : Nat} (hi : i < 32)
    (hg : ∀ k < 5, g k = B.getD (5 * i + k) 0) {e : Nat} (he : e < 8) :
    (decodeDecompress 5 B)[8 * i + e]! =
      decompress 5 (bsum g (fieldAt 5 e).1 (fieldAt 5 e).2.2 / 2 ^ (fieldAt 5 e).2.1 % 2 ^ 5) := by
  have l : ∀ k, (g k).toNat < 256 := fun k => (g k).isLt
  have l0 := l 0; have l1 := l 1; have l2 := l 2; have l3 := l 3; have l4 := l 4
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Nat.add_zero, decodeDecompress5_0 B hB hi, ← Nat.add_zero (5 * i), ← hg 0 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_1 B hB hi, ← Nat.add_zero (5 * i), ← hg 0 (by decide), ← hg 1 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_2 B hB hi, ← hg 1 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_3 B hB hi, ← hg 1 (by decide), ← hg 2 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_4 B hB hi, ← hg 2 (by decide), ← hg 3 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_5 B hB hi, ← hg 3 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_6 B hB hi, ← hg 3 (by decide), ← hg 4 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress5_7 B hB hi, ← hg 4 (by decide)]
    refine congrArg (decompress 5) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega

/-- Field `e` of `ByteDecode₁₁`, from its bytes. -/
theorem fieldVal11 {B : List Byte} (hB : B.length = 352) {i : Nat} (hi : i < 32)
    (hg : ∀ k < 11, g k = B.getD (11 * i + k) 0) {e : Nat} (he : e < 8) :
    (decodeDecompress 11 B)[8 * i + e]! =
      decompress 11 (bsum g (fieldAt 11 e).1 (fieldAt 11 e).2.2 / 2 ^ (fieldAt 11 e).2.1 % 2 ^ 11) := by
  have l : ∀ k, (g k).toNat < 256 := fun k => (g k).isLt
  have l0 := l 0; have l1 := l 1; have l2 := l 2; have l3 := l 3; have l4 := l 4; have l5 := l 5
  have l6 := l 6; have l7 := l 7; have l8 := l 8; have l9 := l 9; have l10 := l 10
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Nat.add_zero, decodeDecompress11_0 B hB hi, ← Nat.add_zero (11 * i), ← hg 0 (by decide),
      ← hg 1 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_1 B hB hi, ← hg 1 (by decide), ← hg 2 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_2 B hB hi, ← hg 2 (by decide), ← hg 3 (by decide), ← hg 4 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_3 B hB hi, ← hg 4 (by decide), ← hg 5 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_4 B hB hi, ← hg 5 (by decide), ← hg 6 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_5 B hB hi, ← hg 6 (by decide), ← hg 7 (by decide), ← hg 8 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_6 B hB hi, ← hg 8 (by decide), ← hg 9 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega
  · rw [decodeDecompress11_7 B hB hi, ← hg 9 (by decide), ← hg 10 (by decide)]
    refine congrArg (decompress 11) ?_
    simp only [fieldAt, bsum, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow]
    omega

end

theorem fieldVal {s₀ : State} (hp : Pre s₀) {i e : Nat} (hi : i < 32) (he : e < 8) :
    (D s₀)[8 * i + e]! = decompress (dd s₀) (bsum (fun k => (bs s₀).getD (dd s₀ * i + k) 0)
      (fieldAt (dd s₀) e).1 (fieldAt (dd s₀) e).2.2 / 2 ^ (fieldAt (dd s₀) e).2.1 % 2 ^ dd s₀) := by
  have hB : (bs s₀).length = 32 * dd s₀ := by rw [bytesAt_length, hp.len]
  rcases mem_widths hp.d with h | h
  · rw [D, h]; rw [h] at hB
    exact fieldVal5 _ hB hi (fun k _ => rfl) he
  · rw [D, h]; rw [h] at hB
    exact fieldVal11 _ hB hi (fun k _ => rfl) he

theorem enc_half : ∀ d ∈ [5, 11], encodable (BitVec.ofNat 32 (2 ^ (d - 1))) = true := by decide

/-- Field `e` of group `i`. -/
theorem field_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) {e : Nat} (he : e < 8) {s : State}
    (h : Mid s₀ i e s) : WP isa (.block (ddField (dd s₀) e)) s (Mid s₀ i (e + 1)) := by
  have hd := mem_widths hp.d
  have hdl : dd s₀ ∈ [5, 11] := by rcases hd with h | h <;> rw [h] <;> decide
  obtain ⟨f1, f2, f3, f4⟩ := fields_ok (dd s₀) hdl e he
  have hl : len s₀ = 32 * dd s₀ := hp.len
  generalize hj : (fieldAt (dd s₀) e).1 = j at f1
  generalize ht : (fieldAt (dd s₀) e).2.1 = t at f2
  generalize hn : (fieldAt (dd s₀) e).2.2 = n at f1 f3 f4
  have bat : ∀ k < n, _ := fun k (hk : k < n) =>
    byte_at hp h.rd h.wr h.frame (S := dd s₀) (i := i) (k := j + k) (by
      have : dd s₀ * i + dd s₀ ≤ dd s₀ * 32 := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
      rw [hl]; rw [Nat.mul_comm 32]; omega)
  obtain ⟨ec, oc, cc⟩ := coeff_at hp h.wr (T := 32) (K := 8) (i := i) rfl (k := e) (by omega)
  let g : Nat → Byte := fun k => (bs s₀).getD (dd s₀ * i + k) 0
  have hsum : bsum g j n / 2 ^ t < 2 ^ 32 := by
    have := bsum_lt g j n
    have : 256 ^ n ≤ 256 ^ 3 := Nat.pow_le_pow_right (by decide) f4
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  unfold ddField
  rw [hj, ht, hn, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loads_ok (g := g) (by omega) f2 ⟨f3, f4⟩ h.r0 (fun k hk => by rw [(bat k hk).1]; exact (bat k hk).2.1)
    (fun k hk => by rw [(bat k hk).1, (bat k hk).2.2.1])) fun s₁ ⟨k₁, v₁⟩ => ?_
  refine WP.mono (mask_ok hd hsum v₁) fun s₂ ⟨k₂, v₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  have hsh : 1 ≤ dd s₀ ∧ dd s₀ ≤ 31 := by rcases hd with h | h <;> omega
  refine WP.mono (store_ok (enc_half _ hdl) hsh (by omega) v₂ (k₁₂.r3.trans h.r3)
    (by rw [ec, k₁₂.wr]; exact oc)) fun s' ⟨r0, r1, r3, pres, m, rd, wr, sp⟩ => ?_
  have hv : dec (dd s₀) (BitVec.ofNat 32 (bsum g j n / 2 ^ t % 2 ^ dd s₀)) = out s₀ (8 * i + e) := by
    unfold out
    rw [dec_eq4 hp.d (n := bsum g j n / 2 ^ t % 2 ^ dd s₀) (by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hsum))
      (Nat.mod_lt _ (Nat.two_pow_pos _)), fieldVal hp hi he, hj, ht, hn]
  refine ⟨r0.trans (k₁₂.r0.trans h.r0), r1.trans (k₁₂.r1.trans h.r1), r3.trans (k₁₂.r3.trans h.r3),
    rd.trans (k₁₂.rd.trans h.rd), wr.trans (k₁₂.wr.trans h.wr), sp.trans (k₁₂.sp.trans h.sp),
    fun r hr => (pres r hr).trans ((k₁₂.pres r hr).trans (h.pres r hr)), ?_, ?_⟩
  · rw [m, ec, k₁₂.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ cc
  · rw [m, ec, k₁₂.mem, hv, ← Nat.add_assoc]
    exact coeff_one (a := 8 * i + e) (by omega) h.coeff rfl

/-- The end of an iteration. -/
theorem tail_ok {s : State} {d : Nat} {x y c : BitVec 32} (hde : encodable (BitVec.ofNat 32 d) = true)
    (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = y) (h1 : s.gpr .r1 = c) :
    WP isa (.block ([.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 d)), .dp .add .r3 .r3 (.imm 32),
      .subs .r1 .r1 (.imm (BitVec.ofNat 32 d))] : List Instr)) s fun s' =>
      s'.gpr .r0 = x + BitVec.ofNat 32 d ∧ s'.gpr .r3 = y + 32 ∧ s'.gpr .r1 = c - BitVec.ofNat 32 d ∧
      s'.z = (c - BitVec.ofNat 32 d == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [hde, h0, h1, h3, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem ddBody_eq (d : Nat) : ddBody d = (List.range 8).flatMap (ddField d) ++
    ([.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 d)), .dp .add .r3 .r3 (.imm 32),
      .subs .r1 .r1 (.imm (BitVec.ofNat 32 d))] : List Instr) := rfl

theorem enc_d : ∀ d ∈ [5, 11], encodable (BitVec.ofNat 32 d) = true := by decide

/-- An iteration of the loop. -/
theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) {s : State} (h : Mid s₀ i 0 s) :
    WP isa (.block (ddBody (dd s₀))) s fun s' => Mid s₀ (i + 1) 0 s' ∧ s'.z = decide (i + 1 = 32) := by
  have hd := mem_widths hp.d
  have hdl : dd s₀ ∈ [5, 11] := by rcases hd with h | h <;> rw [h] <;> decide
  rw [ddBody_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (f := ddField (dd s₀)) (N := 8) (Mid s₀ i)
    (fun e s he hs => field_step hp hi he hs) 8 (Nat.le_refl _) s h) fun s₁ h₁ => ?_
  refine WP.mono (tail_ok (enc_d _ hdl) h₁.r0 h₁.r3 h₁.r1) fun s' ⟨r0, r3, r1, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h₁.rd, wr.trans h₁.wr, sp.trans h₁.sp,
      fun r hr => (pres r hr).trans (h₁.pres r hr), m ▸ h₁.frame, fun j hj => by
        rw [m, h₁.coeff j hj, show 8 * i + 8 = 8 * (i + 1) + 0 by omega]⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ (dd s₀) i
  · rw [r1]; exact count_sub (k := dd s₀) hi
  · rw [r3]; exact ptr_succ _ 32 i
  · rw [z]; exact count_z (k := dd s₀) hi (by omega) (by rcases hd with h | h <;> rw [h] <;> decide)

/-! ## The whole function -/

theorem loop_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (m : s₁.mem = s₀.mem)
    (rd : s₁.rd = s₀.rd) (wr : s₁.wr = s₀.wr) (sp : s₁.sp = s₀.sp) :
    WP isa (.loop (.block (ddBody (dd s₀))) .ne) s₁ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ PolyIs s.mem (F s₀) (D s₀) := by
  refine wp_loop_ne (fun i s => Mid s₀ i 0 s) (N := 32) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ⟨h.pres, h.sp, polyIs_of_coeffAt fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [n_eq] at hj; omega)]; rfl⟩) ?_
  refine ⟨?_, ?_, ?_, rd, wr, sp, fun r _ => by rw [g], by rw [m]; exact Frame.refl _ _,
    fun j _ => by rw [m, Nat.mul_zero, Nat.add_zero, ite_eq_right (Nat.not_lt_zero _)]⟩
  · rw [g]; simp
  · rw [g, Nat.sub_zero, Nat.mul_comm, ← hp.len]; simp [len]
  · rw [g]; simp

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa decodeDecompress1024 s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (D s₀) := by
  have hd := mem_widths hp.d
  unfold decodeDecompress1024
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.ite (decide (dd s₀ = 5)) (by
    show some (s₀.gpr .r2 - BitVec.ofNat 32 5 == 0) = _
    rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
  · have e5 : dd s₀ = 5 := of_decide_eq_true e
    rw [← e5]; exact loop_ok hp rfl rfl rfl rfl rfl
  · have e11 : dd s₀ = 11 := by have := of_decide_eq_false e; omega
    rw [← e11]; exact loop_ok hp rfl rfl rfl rfl rfl

theorem pre_of {s : State} (h : (Spec.MlKem1024.decodeDecompressContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 160 | .r2 => 5 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target decodeDecompress1024
    (Spec.MlKem1024.decodeDecompressContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.Decompress
