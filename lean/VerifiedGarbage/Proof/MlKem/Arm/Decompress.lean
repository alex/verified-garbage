import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_decode_decompress`

Untrusted: everything here is checked by Lean. A loop for each width `d`,
whose body is symbolically executed once for any pointers (`body4_ok`,
`body10_ok`; for `d = 1`, each of the eight bits once for any bit,
`bit_ok`). The invariant says which coefficients are written (`Inv`); their
values are `decompress_val` of the fields of `decodeDecompress1`,
`decodeDecompress4_even`, … .
-/

namespace VG.Proof.MlKem.Arm.Decompress

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The values -/

/-- `(q · y + 2ᵈ⁻¹) >> d`, as `decompressTo` computes it. -/
def dec (d : Nat) (y : BitVec 32) : BitVec 32 :=
  (y + (y <<< 8) + (y <<< 10) + (y <<< 11) + BitVec.ofNat 32 (2 ^ (d - 1))) >>> d

theorem dec_toNat {d : Nat} (hd : d ∈ compressWidths) {y : BitVec 32} (hy : y.toNat < 2 ^ d) :
    (dec d y).toNat = (decompress d y.toNat).val := by
  rw [(decompress_val hd hy).1]
  unfold dec
  rw [q_eq]
  rcases mem_compressWidths hd with rfl | rfl | rfl <;> bv_omega

/-- A decompressed field, as a stored word. -/
theorem dec_eq {d : Nat} (hd : d ∈ compressWidths) {y : BitVec 32} {n : Nat} (hy : y.toNat = n)
    (hn : n < 2 ^ d) : dec d y = BitVec.ofNat 32 (decompress d n).val :=
  ofNat_val_eq (by rw [dec_toNat hd (hy ▸ hn), hy])

/-- Bit `j` of a byte, as `dd1Bit` extracts it. -/
def bit1 (b : Byte) (j : Nat) : BitVec 32 := (b.setWidth 32 <<< (31 - j)) >>> 31

theorem bit1_toNat (b : Byte) {j : Nat} (hj : j < 8) : (bit1 b j).toNat = b.toNat / 2 ^ j % 2 := by
  have hb := b.isLt
  rw [bit1, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega

/-! ## The loop bodies -/

section
variable {s : State} {x y : BitVec 32}

theorem bit_ok {j : Nat} (hj : j < 8) (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = y)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 (4 * j))) 4) :
    WP isa (.block (dd1Bit j)) s fun s' =>
      s'.gpr .r0 = x ∧ s'.gpr .r3 = y ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 (4 * j)))
        (dec 1 (bit1 (s.mem (State.addr (x + BitVec.ofNat 32 0))) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have hsh : 1 ≤ 31 - j ∧ 31 - j ≤ 31 := by omega
  have ho : 4 * j < 4096 := by omega
  run_block [dd1Bit, decompressTo, dec, bit1, h0, h3, i0, o, hsh, ho, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- The end of an iteration of the loop for `d = 1`. -/
def tail1 : List Instr := [.dp .add .r0 .r0 (.imm 1), .dp .add .r3 .r3 (.imm 32), .subs .r1 .r1 (.imm 1)]

theorem dd1Body_eq : dd1Body = (List.range 8).flatMap dd1Bit ++ tail1 := rfl

theorem tail1_ok {c : BitVec 32} (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = y) (h1 : s.gpr .r1 = c) :
    WP isa (.block tail1) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r3 = y + 32 ∧ s'.gpr .r1 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [tail1, h0, h1, h3, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem body4_ok {c : BitVec 32} (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = y) (h1 : s.gpr .r1 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (hsep : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v) (State.addr (x + BitVec.ofNat 32 0)) =
        m (State.addr (x + BitVec.ofNat 32 0))) :
    WP isa (.block dd4Body) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r3 = y + 8 ∧ s'.gpr .r1 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (dec 4 (((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 <<< 28) >>> 28))).writeW
        (State.addr (y + BitVec.ofNat 32 4)) (dec 4 ((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 >>> 4)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [dd4Body, decompressTo, dec, h0, h1, h3, i0, o0, o1, hsep, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- The four fields of a group of five bytes `b`, as `dd10Body` extracts them. -/
def f10 (b : Nat → Byte) (k : Nat) : BitVec 32 :=
  if k = 0 then ((b 1).setWidth 32 <<< 30 >>> 22) + (b 0).setWidth 32
  else if k = 1 then ((b 2).setWidth 32 <<< 28 >>> 22) + ((b 1).setWidth 32 >>> 2)
  else if k = 2 then ((b 3).setWidth 32 <<< 26 >>> 22) + ((b 2).setWidth 32 >>> 4)
  else ((b 4).setWidth 32 <<< 2) + ((b 3).setWidth 32 >>> 6)

theorem body10_ok {c : BitVec 32} (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = y) (h1 : s.gpr .r1 = c)
    (ib : ∀ k < 5, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 k)) 1)
    (o0 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 4)) 4)
    (o2 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 8)) 4)
    (o3 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 12)) 4)
    (hsep : ∀ (m : Mem) (o : Nat) (v : BitVec 32) (k : Nat), o < 12 → k < 5 →
      (m.writeW (State.addr (y + BitVec.ofNat 32 o)) v) (State.addr (x + BitVec.ofNat 32 k)) =
        m (State.addr (x + BitVec.ofNat 32 k))) :
    WP isa (.block dd10Body) s fun s' =>
      s'.gpr .r0 = x + 5 ∧ s'.gpr .r3 = y + 16 ∧ s'.gpr .r1 = c - 5 ∧ s'.z = (c - 5 == 0) ∧
      s'.mem = (((s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (dec 10 (f10 (fun k => s.mem (State.addr (x + BitVec.ofNat 32 k))) 0))).writeW
        (State.addr (y + BitVec.ofNat 32 4)) (dec 10 (f10 (fun k => s.mem (State.addr (x + BitVec.ofNat 32 k))) 1))).writeW
        (State.addr (y + BitVec.ofNat 32 8)) (dec 10 (f10 (fun k => s.mem (State.addr (x + BitVec.ofNat 32 k))) 2))).writeW
        (State.addr (y + BitVec.ofNat 32 12)) (dec 10 (f10 (fun k => s.mem (State.addr (x + BitVec.ofNat 32 k))) 3)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have i0 := ib 0 (by omega)
  have i1 := ib 1 (by omega)
  have i2 := ib 2 (by omega)
  have i3 := ib 3 (by omega)
  have i4 := ib 4 (by omega)
  run_block [dd10Body, dd10Field, decompressTo, dec, f10, h0, h1, h3, i0, i1, i2, i3, i4, o0, o1, o2, o3,
    hsep, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self,
    and_true]

end

/-! ## The loops -/

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
  d : dd s₀ ∈ compressWidths
  len : len s₀ = 32 * dd s₀

/-- After `i` iterations of the loop that reads `S` bytes and writes `K`
coefficients (`T = 4K` bytes) each time, of `N`. -/
structure Inv (S T K N : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (S * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (S * (N - i))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (T * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < K * i then out s₀ j else coeffAt s₀.mem (F s₀) j

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

/-- A store to the output leaves the input. -/
theorem sep_at {N : Nat} (hT : T = 4 * K) {o k : Nat} (ho : o + 4 ≤ T) (hk : S * i + k < len s₀)
    (hi : i < N) (hKN : K * N = 256) (m : Mem) (v : BitVec 32) :
    (m.writeW (State.addr (pf s₀ + BitVec.ofNat 32 (T * i) + BitVec.ofNat 32 o)) v)
      (State.addr (pb s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 k)) =
      m (State.addr (pb s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 k)) := by
  have fF := hp.fitF
  have hTi : T * i + T ≤ 1024 := by
    subst hT
    have : K * i + K ≤ K * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [Nat.mul_assoc]
    omega
  rw [(byte_at hp hrd hwr hf hk).1, addr_byte (len := 1024) fF rfl (by omega)]
  exact byte_writeW_disj hp.disj v (contains_off (by omega) (by omega)) (byte_at hp hrd hwr hf hk).2.2.2

end

/-- The whole loop, from its steps. -/
theorem loop_of {s₀ : State} {S T K N : Nat} {body : List Instr} (hN : 0 < N)
    (hKN : K * N = 256) (hlen : len s₀ = S * N)
    (hstep : ∀ i < N, ∀ s, Inv S T K N s₀ i s →
      WP isa (.block body) s fun s' => Inv S T K N s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = N))
    {s₁ : State} (g : s₁.gpr = s₀.gpr) (m : s₁.mem = s₀.mem) (rd : s₁.rd = s₀.rd) (wr : s₁.wr = s₀.wr)
    (sp : s₁.sp = s₀.sp) :
    WP isa (.loop (.block body) .ne) s₁ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ PolyIs s.mem (F s₀) (D s₀) := by
  refine wp_loop_ne (Inv S T K N s₀) hN hstep (fun s h => ⟨h.pres, h.sp,
    polyIs_of_coeffAt fun j hj => by
      rw [h.coeff j hj, ite_eq_left (by rw [hKN]; rw [n_eq] at hj; exact hj)]; rfl⟩) ?_
  · refine ⟨?_, ?_, ?_, rd, wr, sp, fun r _ => by rw [g], by rw [m]; exact Frame.refl _ _,
      fun j _ => by rw [m, Nat.mul_zero, ite_eq_right (Nat.not_lt_zero _)]⟩
    · rw [g]; simp
    · rw [g, Nat.sub_zero, ← hlen]; simp [len]
    · rw [g]; simp

/-! ## Each width -/

theorem step4 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 4) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv 1 8 2 128 s₀ i s) :
    WP isa (.block dd4Body) s fun s' => Inv 1 8 2 128 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have hl : len s₀ = 128 := by rw [hp.len, hd]
  have hB : (bs s₀).length = 128 := by rw [bytesAt_length, hl]
  obtain ⟨eb, ib, rb, -⟩ := byte_at hp h.rd h.wr h.frame (S := 1) (i := i) (k := 0) (by omega)
  obtain ⟨e0, o0, c0⟩ := coeff_at hp h.wr (T := 8) (K := 2) (i := i) rfl (k := 0) (by omega)
  obtain ⟨e1, o1, c1⟩ := coeff_at hp h.wr (T := 8) (K := 2) (i := i) rfl (k := 1) (by omega)
  rw [Nat.add_zero] at eb rb e0 o0 c0
  have v0 : dec 4 ((((bs s₀).getD (1 * i) 0).setWidth 32 <<< 28) >>> 28) = out s₀ (2 * i) := by
    have hb := ((bs s₀).getD (1 * i) 0).isLt
    unfold out
    rw [Nat.one_mul] at hb ⊢
    rw [dec_eq (d := 4) (by decide) (n := ((bs s₀).getD i 0).toNat % 16) (by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq]; omega) (by omega), D, hd, decodeDecompress4_even _ hB hi]
  have v1 : dec 4 (((bs s₀).getD (1 * i) 0).setWidth 32 >>> 4) = out s₀ (2 * i + 1) := by
    have hb := ((bs s₀).getD (1 * i) 0).isLt
    unfold out
    rw [Nat.one_mul] at hb ⊢
    rw [dec_eq (d := 4) (by decide) (n := ((bs s₀).getD i 0).toNat / 16) (by
      rw [BitVec.toNat_ushiftRight, setWidth32_toNat, Nat.shiftRight_eq_div_pow]) (by omega), D, hd,
      decodeDecompress4_odd _ hB hi]
  refine WP.mono (body4_ok h.r0 h.r3 h.r1 (by rw [eb]; exact ib) (by rw [e0]; exact o0)
    (by rw [e1]; exact o1) (fun m v => sep_at hp h.rd h.wr h.frame (S := 1) (T := 8) (K := 2) rfl (by omega) (by omega) hi rfl m v))
    fun s' ⟨r0, r3, r1, z, m, rd, wr, sp, pres⟩ => ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 i
  · rw [r1]; exact count_sub (k := 1) hi
  · rw [r3]; exact ptr_succ _ 8 i
  · rw [m, e0, e1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  · rw [m, e0, e1, eb, rb, v0, v1]
    exact coeff_one (a := 2 * i + 1) (by omega) (coeff_one (a := 2 * i) (by omega) h.coeff rfl) rfl
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem f10_congr {b b' : Nat → Byte} (h : ∀ k < 5, b k = b' k) (j : Nat) : f10 b j = f10 b' j := by
  unfold f10
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem f10_toNat (g : Nat → Byte) :
    (f10 g 0).toNat = (g 0).toNat + 256 * ((g 1).toNat % 4) ∧
    (f10 g 1).toNat = (g 1).toNat / 4 + 64 * ((g 2).toNat % 16) ∧
    (f10 g 2).toNat = (g 2).toNat / 16 + 16 * ((g 3).toNat % 64) ∧
    (f10 g 3).toNat = (g 3).toNat / 64 + 4 * (g 4).toNat := by
  have := (g 0).isLt
  have := (g 1).isLt
  have := (g 2).isLt
  have := (g 3).isLt
  have := (g 4).isLt
  simp (config := {decide := true}) only [f10, ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 10) {i : Nat} (hi : i < 64) {s : State}
    (h : Inv 5 16 4 64 s₀ i s) :
    WP isa (.block dd10Body) s fun s' => Inv 5 16 4 64 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 64) := by
  have hl : len s₀ = 320 := by rw [hp.len, hd]
  have hB : (bs s₀).length = 320 := by rw [bytesAt_length, hl]
  have bat : ∀ k < 5, _ := fun k (hk : k < 5) =>
    byte_at hp h.rd h.wr h.frame (S := 5) (i := i) (k := k) (by omega)
  obtain ⟨e0, o0, c0⟩ := coeff_at hp h.wr (T := 16) (K := 4) (i := i) rfl (k := 0) (by omega)
  obtain ⟨e1, o1, c1⟩ := coeff_at hp h.wr (T := 16) (K := 4) (i := i) rfl (k := 1) (by omega)
  obtain ⟨e2, o2, c2⟩ := coeff_at hp h.wr (T := 16) (K := 4) (i := i) rfl (k := 2) (by omega)
  obtain ⟨e3, o3, c3⟩ := coeff_at hp h.wr (T := 16) (K := 4) (i := i) rfl (k := 3) (by omega)
  rw [Nat.add_zero] at e0 o0 c0
  let g : Nat → Byte := fun k => (bs s₀).getD (5 * i + k) 0
  have hg : ∀ k < 5, (fun k => s.mem (State.addr (pb s₀ + BitVec.ofNat 32 (5 * i) + BitVec.ofNat 32 k))) k =
      g k := fun k hk => by
    show s.mem _ = _
    rw [(bat k hk).1, (bat k hk).2.2.1]
  obtain ⟨t0, t1, t2, t3⟩ := f10_toNat g
  have lg : ∀ k, (g k).toNat < 256 := fun k => (g k).isLt
  have v : ∀ k < 4, dec 10 (f10 g k) = out s₀ (4 * i + k) := by
    intro k hk
    unfold out
    have l0 := lg 0; have l1 := lg 1; have l2 := lg 2; have l3 := lg 3; have l4 := lg 4
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [dec_eq (d := 10) (by decide) t0 (by omega), D, hd, Nat.add_zero, decodeDecompress10_0 _ hB hi]
      rfl
    · rw [dec_eq (d := 10) (by decide) t1 (by omega), D, hd, decodeDecompress10_1 _ hB hi]
    · rw [dec_eq (d := 10) (by decide) t2 (by omega), D, hd, decodeDecompress10_2 _ hB hi]
    · rw [dec_eq (d := 10) (by decide) t3 (by omega), D, hd, decodeDecompress10_3 _ hB hi]
  refine WP.mono (body10_ok h.r0 h.r3 h.r1 (fun k hk => by rw [(bat k hk).1]; exact (bat k hk).2.1)
    (by rw [e0]; exact o0) (by rw [e1]; exact o1) (by rw [e2]; exact o2) (by rw [e3]; exact o3)
    (fun m o v k ho hk => sep_at hp h.rd h.wr h.frame (S := 5) (T := 16) (K := 4) rfl (by omega)
      (by omega) hi rfl m v))
    fun s' ⟨r0, r3, r1, z, m, rd, wr, sp, pres⟩ => ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 5 i
  · rw [r1]; exact count_sub (k := 5) hi
  · rw [r3]; exact ptr_succ _ 16 i
  · rw [m, e0, e1, e2, e3]
    exact (((h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1).writeW
      (List.mem_singleton_self _) _ c2).writeW (List.mem_singleton_self _) _ c3
  · rw [m, e0, e1, e2, e3, f10_congr hg, f10_congr hg, f10_congr hg, f10_congr hg, v 0 (by omega),
      v 1 (by omega), v 2 (by omega), v 3 (by omega), Nat.add_zero]
    exact coeff_one (a := 4 * i + 3) (by omega) (coeff_one (a := 4 * i + 2) (by omega)
      (coeff_one (a := 4 * i + 1) (by omega) (coeff_one (a := 4 * i) (by omega) h.coeff rfl) rfl) rfl) rfl
  · rw [z]; exact count_z (k := 5) hi (by decide) (by decide)

/-- Within an iteration of the loop for `d = 1`, after the first `a` bits
of the byte. -/
structure Mid (s₀ : State) (i a : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pb s₀ + BitVec.ofNat 32 (1 * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (1 * (32 - i))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < 8 * i + a then out s₀ j else coeffAt s₀.mem (F s₀) j

theorem bit_step {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 1) {i : Nat} (hi : i < 32) {a : Nat}
    (ha : a < 8) {s : State} (h : Mid s₀ i a s) : WP isa (.block (dd1Bit a)) s (Mid s₀ i (a + 1)) := by
  have hl : len s₀ = 32 := by rw [hp.len, hd]
  obtain ⟨eb, ib, rb, -⟩ := byte_at hp h.rd h.wr h.frame (S := 1) (i := i) (k := 0) (by omega)
  obtain ⟨e, o, c⟩ := coeff_at hp h.wr (T := 32) (K := 8) (i := i) rfl (k := a) (by omega)
  rw [Nat.add_zero] at eb rb
  have v : dec 1 (bit1 ((bs s₀).getD (1 * i) 0) a) = out s₀ (8 * i + a) := by
    unfold out
    rw [dec_eq (d := 1) (by decide) (bit1_toNat _ ha) (Nat.mod_lt _ (by decide)), D, hd,
      decodeDecompress1 _ (by rw [n_eq]; omega), show (8 * i + a) / 8 = i by omega,
      show (8 * i + a) % 8 = a by omega, Nat.one_mul]
  refine WP.mono (bit_ok ha h.r0 h.r3 (by rw [eb]; exact ib) (by rw [e]; exact o))
    fun s' ⟨r0, r3, r1, m, rd, wr, sp, pres⟩ => ⟨r0, r1.trans h.r1, r3,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩
  · rw [m, e]; exact h.frame.writeW (List.mem_singleton_self _) _ c
  · rw [m, e, eb, rb, v]; exact coeff_one (a := 8 * i + a) (by omega) h.coeff rfl

theorem step1 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 1) {i : Nat} (hi : i < 32) {s : State}
    (h : Inv 1 32 8 32 s₀ i s) :
    WP isa (.block dd1Body) s fun s' => Inv 1 32 8 32 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 32) := by
  rw [dd1Body_eq, WP.block_append_iff]
  have h0 : Mid s₀ i 0 s := ⟨h.r0, h.r1, h.r3, h.rd, h.wr, h.sp, h.pres, h.frame, h.coeff⟩
  refine WP.mono (wp_range_flatMap (M := isa) (f := dd1Bit) (N := 8) (Mid s₀ i)
    (fun a s ha hs => bit_step hp hd hi ha hs) 8 (Nat.le_refl _) s h0) fun s₁ h₁ => ?_
  refine WP.mono (tail1_ok h₁.r0 h₁.r3 h₁.r1) fun s' ⟨r0, r3, r1, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h₁.rd, wr.trans h₁.wr, sp.trans h₁.sp,
      fun r hr => (pres r hr).trans (h₁.pres r hr), m ▸ h₁.frame, m ▸ h₁.coeff⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 i
  · rw [r1]; exact count_sub (k := 1) hi
  · rw [r3]; exact ptr_succ _ 32 i
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa decodeDecompress s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (D s₀) := by
  have hd := mem_compressWidths hp.d
  unfold Impl.MlKem.Arm.decodeDecompress
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.ite (decide (dd s₀ = 1)) (by
    show some (s₀.gpr .r2 - BitVec.ofNat 32 1 == 0) = _
    rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
  · exact loop_of (N := 32) (by decide) (by decide) (by rw [hp.len, of_decide_eq_true e])
      (fun i hi s h => step1 hp (of_decide_eq_true e) hi h) rfl rfl rfl rfl rfl
  · have e1 : dd s₀ ≠ 1 := of_decide_eq_false e
    refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
    refine WP.ite (decide (dd s₀ = 4)) (by
      show some (s₀.gpr .r2 - BitVec.ofNat 32 4 == 0) = _
      rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
    · exact loop_of (N := 128) (by decide) (by decide) (by rw [hp.len, of_decide_eq_true e])
        (fun i hi s h => step4 hp (of_decide_eq_true e) hi h) rfl rfl rfl rfl rfl
    · have e10 : dd s₀ = 10 := by have := of_decide_eq_false e; omega
      exact loop_of (N := 64) (by decide) (by decide) (by rw [hp.len, e10])
        (fun i hi s h => step10 hp e10 hi h) rfl rfl rfl rfl rfl

theorem pre_of {s : State} (h : (Spec.MlKem.decodeDecompressContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 1 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.decodeDecompress
    (Spec.MlKem.decodeDecompressContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_pre [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
      by decide⟩

end VG.Proof.MlKem.Arm.Decompress
