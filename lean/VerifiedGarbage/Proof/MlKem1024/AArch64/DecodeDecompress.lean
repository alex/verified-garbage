import VerifiedGarbage.Proof.MlKem1024.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decode_decompress`

Untrusted: everything here is checked by Lean. Group `g` of the input is
the number whose bytes are its `d` bytes (`num g d`), and coefficient `e`
of the group is its base-`2ᵈ` digit `e` (`byteDecode_group`), decompressed.
Before coefficient `e`, `x9` holds the bits of the first `⌈d e / 8⌉` bytes
above the first `d e` (`DInv`); the bytes coefficient `e` needs are added
above them (`byte_step`), and its digit is decompressed and shifted out
(`coeff_step`).
-/

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem1024_decode_decompress(b = x0, len = x1,
d = w2, f = x3)`: if `d` is 5 or 11 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`,
reduced. The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ Spec.MlKem1024.compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem1024.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (d : Nat) (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x3
abbrev bR : Region := ⟨bP s₀, 32 * d⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (32 * d)
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B d s₀).getD j 0).toNat
/-- The first `j` bytes of group `g`, as a little-endian number. -/
def num (g j : Nat) : Nat := digits 8 ((List.range j).map fun j' => byte d s₀ (d * g + j'))
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress d (B d s₀))[i]!).val
/-- The output's coefficients before. -/
def old (i : Nat) : BitVec 32 := coeffAt s₀.mem (fP s₀) i

end

structure Pre (d : Nat) (s₀ : State) : Prop where
  hd : d = 5 ∨ d = 11
  rd : s₀.rd = [bR d s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR d s₀).Disjoint (polyRegion (fP s₀))
  x5 : (s₀.gpr .x5).toNat = q

/-- After `g` groups. -/
structure Inv (d : Nat) (s₀ : State) (g : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (d * g)
  x3 : s.gpr .x3 = fP s₀ + BitVec.ofNat 64 (32 * g)
  x5 : (s.gpr .x5).toNat = q
  x6 : (s.gpr .x6).toNat = 2 ^ (d - 1)
  x7 : (s.gpr .x7).toNat = 2 ^ d - 1
  x11 : (s.gpr .x11).toNat = 32 - g
  out : CoeffsUpTo s.mem (fP s₀) (8 * g) (G d s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

theorem num_succ (d : Nat) (s₀ : State) (g j : Nat) :
    num d s₀ g (j + 1) = num d s₀ g j + 2 ^ (8 * j) * byte d s₀ (d * g + j) :=
  digits_range_succ _ _ _

theorem num_lt (d : Nat) (s₀ : State) (g j : Nat) : num d s₀ g j < 2 ^ (8 * j) :=
  digits_range_lt (fun _ => byte_lt _) _

theorem num_mod (d : Nat) (s₀ : State) (g : Nat) {j j' : Nat} (h : j ≤ j') :
    num d s₀ g j' % 2 ^ (8 * j) = num d s₀ g j :=
  digits_range_mod (fun _ => byte_lt _) h

/-- Coefficient `e` of group `g` of the output. -/
theorem G_eq {d : Nat} (hd : d = 5 ∨ d = 11) (s₀ : State) {g e : Nat} (hg : g < 32) (he : e < 8) :
    G d s₀ (8 * g + e) =
      BitVec.ofNat 32 ((q * (num d s₀ g d / 2 ^ (d * e) % 2 ^ d) + 2 ^ (d - 1)) / 2 ^ d) := by
  have hi : 8 * g + e < 256 := by omega
  have hd12 : d < 12 := by omega
  have hdw : d ∈ Spec.MlKem1024.compressWidths := by rcases hd with rfl | rfl <;> decide
  rw [G, decodeDecompress_get _ _ (show _ < n from hi),
    byteDecode_group (c := 8) (b := d) (Nat.mul_comm d 8) _ he (show _ < n from hi),
    bytes_map_take_drop _ (by rw [bytesAt_length]; rcases hd with rfl | rfl <;> omega),
    ite_eq_left hd12, Nat.mod_mod,
    (decompress1024_val hdw (Nat.mod_lt _ (Nat.two_pow_pos _))).1]
  rfl

theorem Pre.byte_eq {d : Nat} {s₀ : State} (hp : Pre d s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {j : Nat} (hj : j < 32 * d) :
    (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte d s₀ j := by
  rw [byte_frame (len := 32 * d) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by rcases hp.hd with rfl | rfl <;> omega) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) (32 * d)).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

/-- Within group `g`, before coefficient `e`. -/
structure DInv (d : Nat) (s₀ : State) (g : Nat) (s : State) (e : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = num d s₀ g (ddJ d e) / 2 ^ (d * e)
  out : CoeffsUpTo t.mem (fP s₀) (8 * g + e) (G d s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem t.mem

/-- Within coefficient `e` of group `g`, after `k` of the bytes it needs. -/
structure LInv (d : Nat) (s₀ : State) (g : Nat) (s : State) (e k : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = num d s₀ g (ddJ d e + k) / 2 ^ (d * e)
  out : CoeffsUpTo t.mem (fP s₀) (8 * g + e) (G d s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem t.mem

theorem ddJ_le (d e : Nat) : ddJ d e ≤ ddJ d (e + 1) := by
  unfold ddJ; rw [Nat.mul_succ]; omega

/-- Byte `k` of those coefficient `e` of group `g` needs, into `x9` above its bits. -/
theorem byte_step {d : Nat} {s₀ : State} (hp : Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : Inv d s₀ g s) (e : Nat) (he : e < 8) (k : Nat) (t : State)
    (hk : k < ddJ d (e + 1) - ddJ d e) (ht : LInv d s₀ g s e k t) :
    WP isa (.block (ddByte d e (ddJ d e + k))) t (LInv d s₀ g s e (k + 1)) := by
  have hd := hp.hd
  have hJ : ddJ d e + k < ddJ d (e + 1) := by omega
  have hde : d * e ≤ 8 * (ddJ d e + k) := by unfold ddJ; omega
  have hsh : 8 * (ddJ d e + k) - d * e < d := by
    have : 8 * ddJ d (e + 1) ≤ d * (e + 1) + 7 := by unfold ddJ; omega
    rw [Nat.mul_succ] at this
    omega
  have hjd : ddJ d e + k < d := by
    have : ddJ d (e + 1) ≤ d := by
      unfold ddJ; rw [Nat.mul_succ]; rcases hd with rfl | rfl <;> omega
    omega
  have hN : d * g + (ddJ d e + k) < 32 * d := by rcases hd with rfl | rfl <;> omega
  have hj4 : ddJ d e + k < 4096 := by rcases hd with rfl | rfl <;> omega
  have hd11 : d ≤ 11 := by omega
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 (d * g + (ddJ d e + k))) hj4
    (by rw [ht.keep.get .x0, h.x0, ptr_add]) ?_ fun t₁ h₁ e₁ => ?_
  · rw [ht.keep.rd, ht.keep.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by omega)))
  have v₁ : (t₁.gpr .x10).toNat = byte d s₀ (d * g + (ddJ d e + k)) := by
    rw [e₁, toNat_byte, hp.byte_eq ht.frame hN]
  have hb := byte_lt ((B d s₀).getD (d * g + (ddJ d e + k)) 0)
  have p8 : 2 ^ (8 * (ddJ d e + k) - d * e) ≤ 1024 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : 8 * (ddJ d e + k) - d * e ≤ 10))
      (by decide)
  have hlt : byte d s₀ (d * g + (ddJ d e + k)) * 2 ^ (8 * (ddJ d e + k) - d * e) ≤ 255 * 1024 :=
    Nat.mul_le_mul (Nat.le_of_lt_succ hb) p8
  refine wp_lsl (by omega) fun t₂ h₂ e₂ => wp_add fun t₃ h₃ e₃ => wp_nil ?_
  have v₂ : (t₂.gpr .x10).toNat = byte d s₀ (d * g + (ddJ d e + k)) * 2 ^ (8 * (ddJ d e + k) - d * e) := by
    rw [e₂, toNat_lsl_n (by rw [v₁]; omega), v₁]
  have hx9 : num d s₀ g (ddJ d e + k) / 2 ^ (d * e) < 1024 :=
    Nat.lt_of_lt_of_le (div_lt_sub (num_lt d s₀ g _) hde) p8
  have m₃ : t₃.mem = t.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine ⟨((ht.keep.trans h₁.keep).trans (h₂.keep.trans h₃.keep)).mono, ?_, by rw [m₃]; exact ht.out,
    by rw [m₃]; exact ht.frame⟩
  rw [e₃, h₂.get .x9, h₁.get .x9, toNat_add_n (by rw [ht.x9, v₂]; omega), ht.x9, v₂,
    add_byte_div hde, ← num_succ, Nat.add_assoc]

/-- Coefficient `e` of group `g`, decompressed, and its bits shifted out. -/
theorem coeff_step {d : Nat} {s₀ : State} (hp : Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : Inv d s₀ g s) (e : Nat) (he : e < 8) (t : State)
    (ht : LInv d s₀ g s e (ddJ d (e + 1) - ddJ d e) t) :
    WP isa (.block (ddCoeff d e)) t (DInv d s₀ g s (e + 1)) := by
  have hd := hp.hd
  have hi : 8 * g + e < 256 := by omega
  have hq : q = 3329 := rfl
  have hJ : ddJ d e + (ddJ d (e + 1) - ddJ d e) = ddJ d (e + 1) := by
    have := ddJ_le d e; omega
  have x9 : (t.gpr .x9).toNat = num d s₀ g (ddJ d (e + 1)) / 2 ^ (d * e) := by rw [ht.x9, hJ]
  have hJd : ddJ d (e + 1) ≤ d := by unfold ddJ; rw [Nat.mul_succ]; rcases hd with rfl | rfl <;> omega
  have hJ8 : d * e + d ≤ 8 * ddJ d (e + 1) := by unfold ddJ; rw [Nat.mul_succ]; omega
  have hy : num d s₀ g (ddJ d (e + 1)) / 2 ^ (d * e) % 2 ^ d = num d s₀ g d / 2 ^ (d * e) % 2 ^ d :=
    bits_of_mod (by rw [num_mod d s₀ g hJd, Nat.mod_eq_of_lt (num_lt d s₀ g _)]) hJ8
  have hyl : num d s₀ g d / 2 ^ (d * e) % 2 ^ d < 2048 := by
    have := Nat.mod_lt (num d s₀ g d / 2 ^ (d * e)) (Nat.two_pow_pos d)
    have : 2 ^ d ≤ 2048 := by rcases hd with rfl | rfl <;> decide
    omega
  have h6 : 2 ^ (d - 1) ≤ 1024 := by rcases hd with rfl | rfl <;> decide
  refine wp_and fun t₁ h₁ e₁ => wp_mul fun t₂ h₂ e₂ => wp_add fun t₃ h₃ e₃ =>
    wp_lsr (by omega) fun t₄ h₄ e₄ => ?_
  have k₄ := (((ht.keep.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep
  have y : (t₁.gpr .x10).toNat = num d s₀ g d / 2 ^ (d * e) % 2 ^ d := by
    rw [e₁, toNat_and_mask _ _ (by rw [ht.keep.get .x7, h.x7]), x9, hy]
  have v₂ : (t₂.gpr .x10).toNat = num d s₀ g d / 2 ^ (d * e) % 2 ^ d * q := by
    rw [e₂, toNat_mul_n (by rw [y, h₁.get .x5, ht.keep.get .x5, h.x5, hq]; omega), y,
      h₁.get .x5, ht.keep.get .x5, h.x5]
  have v₃ : (t₃.gpr .x10).toNat = num d s₀ g d / 2 ^ (d * e) % 2 ^ d * q + 2 ^ (d - 1) := by
    have x6 : (t₂.gpr .x6).toNat = 2 ^ (d - 1) := by
      rw [h₂.get .x6, h₁.get .x6, ht.keep.get .x6, h.x6]
    rw [e₃, toNat_add_n (by rw [v₂, x6, hq]; omega), v₂, x6]
  refine wp_strw (a := coeffAddr (fP s₀) (8 * g + e)) ⟨by omega, by omega⟩ ?_ ?_ fun t₅ h₅ =>
    wp_lsr (by omega) fun t₆ h₆ e₆ => wp_nil ?_
  · rw [k₄.get .x3, h.x3, ptr_add, coeffAddr, Nat.mul_add, ← Nat.mul_assoc]
  · rw [k₄.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (coeff_contains _ (show _ < n from hi))
  have v₄ : (t₄.gpr .x10).setWidth 32 = G d s₀ (8 * g + e) := by
    rw [setWidth32_of_toNat (by rw [e₄, toNat_lsr, v₃]), G_eq hd s₀ hg he, Nat.mul_comm q]
  have m₄ : t₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨(k₄.trans (h₅.keep.trans h₆.keep)).mono, ?_, ?_, ?_⟩
  · rw [e₆, toNat_lsr, h₅.gpr, h₄.get .x9, h₃.get .x9, h₂.get .x9, h₁.get .x9, x9,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [h₆.mem, h₅.mem, m₄, v₄, ← Nat.add_assoc]
    exact ht.out.write (by omega) rfl
  · rw [h₆.mem, h₅.mem, m₄]
    exact ht.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show _ < n from hi))

/-- The bytes coefficient `e` of group `g` needs, and the coefficient. -/
theorem coeffs_step {d : Nat} {s₀ : State} (hp : Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : Inv d s₀ g s) (e : Nat) (t : State) (he : e < 8) (ht : DInv d s₀ g s e t) :
    WP isa (.block (ddStep d e)) t (DInv d s₀ g s (e + 1)) := by
  rw [ddStep, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (f := fun k => ddByte d e (ddJ d e + k)) (LInv d s₀ g s e)
    (fun k u hk hu => byte_step hp hg h e he k u hk hu) _ (Nat.le_refl _) t
    ⟨ht.keep, by rw [Nat.add_zero]; exact ht.x9, ht.out, ht.frame⟩) fun t₁ h₁ => ?_
  exact coeff_step hp hg h e he t₁ h₁

theorem ddBody_eq (d : Nat) : ddBody d = .movz .x .x9 0 0 :: ((List.range 8).flatMap (ddStep d) ++
    ([.addImm .x .x0 .x0 d, .addImm .x .x3 .x3 32, .subImm .x .x11 .x11 1] : List Instr)) := by
  simp only [ddBody, List.cons_append]

/-- One group. -/
theorem step {d : Nat} {s₀ : State} (hp : Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : Inv d s₀ g s) :
    WP isa (.block (ddBody d)) s fun s' =>
      Inv d s₀ (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 32) := by
  have hd := hp.hd
  rw [ddBody_eq]
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (DInv d s₀ g s)
    (fun e t he ht => coeffs_step hp hg h e t he ht) 8 (Nat.le_refl _) s₁
    ⟨h₁.keep.mono, by
      rw [e₁, toNat_imm]; simp only [num, ddJ, Nat.mul_zero, Nat.zero_add, Nat.reduceDiv, List.range_zero,
        List.map_nil, digits_nil, Nat.zero_div]; rfl,
      by rw [h₁.mem, Nat.add_zero]; exact h.out, by rw [h₁.mem]; exact h.frame⟩)
    fun s₂ h₂ => ?_
  refine wp_addImm (by rcases hd with rfl | rfl <;> decide) fun s₃ h₃ e₃ => wp_addImm (by decide)
    fun s₄ h₄ e₄ => wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  have k₄ := (h₂.keep.trans h₃.keep).trans h₄.keep
  have c11 : (s₄.gpr .x11).toNat = 32 - g := by rw [k₄.get .x11, h.x11]
  have v11 : (s₅.gpr .x11).toNat = 32 - (g + 1) := by
    rw [e₅, toNat_sub_n (by rw [c11]; simp; omega), c11]
    simp
    omega
  have k₅ := k₄.trans h₅.keep
  refine ⟨⟨by rw [k₅.rd, h.rd], by rw [k₅.wr, h.wr], by rw [k₅.sp, h.sp], ?_, ?_,
    by rw [k₅.get .x5, h.x5], by rw [k₅.get .x6, h.x6], by rw [k₅.get .x7, h.x7], v11, ?_, ?_⟩,
    by rw [v11]; omega⟩
  · rw [h₅.get .x0, h₄.get .x0, e₃, h₂.keep.get .x0, h.x0, ptr_next]
  · rw [h₅.get .x3, e₄, h₃.get .x3, h₂.keep.get .x3, h.x3, ptr_next]
  · rw [h₅.mem, h₄.mem, h₃.mem, Nat.mul_succ]
    exact h₂.out
  · rw [h₅.mem, h₄.mem, h₃.mem]
    exact h₂.frame

/-- The loop: `Decompress_d(ByteDecode_d(B))` into the output. -/
theorem loop_ok {d : Nat} {s₀ : State} (hp : Pre d s₀) :
    WP isa (ddLoop d) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      PolyIs s'.mem (fP s₀) (decodeDecompress d (B d s₀)) := by
  have hd := hp.hd
  refine WP.seq ?_
  rw [List.append_assoc]
  refine wp_movImm fun s₁ h₁ e₁ => wp_movImm fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_
  refine WP.mono (count_loop (by decide) (Inv d s₀) (fun g hg s h => step hp hg h) ?_)
    fun s' h => ⟨h.rd, h.wr, h.sp, h.out.polyIs fun _ _ => rfl⟩
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s₀.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have p6 : 2 ^ (d - 1) < 2 ^ 64 := by rcases hd with rfl | rfl <;> decide
  have p7 : 2 ^ d - 1 < 2 ^ 64 := by rcases hd with rfl | rfl <;> decide
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₃.get .x3, Nat.mul_zero, ptr_zero], by rw [k₃.get .x5, hp.x5],
    by rw [h₃.get .x6, h₂.get .x6, e₁, toNat_ofNat_lt p6], by rw [h₃.get .x7, e₂, toNat_ofNat_lt p7],
    by rw [e₃, toNat_imm]; rfl, ?_, ?_⟩
  · rw [m₃, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · rw [m₃]; exact Frame.refl _ _

/-- One width, from the state after the dispatch. -/
theorem width_ok {d : Nat} (hd : d = 5 ∨ d = 11) {s₀ s : State} (hs : decodeDecompressAArch64.pre s₀)
    (hdd : ((s₀.gpr .x2).setWidth 32).toNat = d) (hk : Keep [.x5, .x9] s₀ s) (hm : s.mem = s₀.mem)
    (h5 : (s.gpr .x5).toNat = q) :
    WP isa (ddLoop d) s fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      decodeDecompressAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, hlen⟩ := hs
  rw [hdd] at hlen
  have e0 : bP s = s₀.gpr .x0 := hk.get .x0
  have e3 : fP s = s₀.gpr .x3 := hk.get .x3
  have hp : Pre d s :=
    ⟨hd, by rw [hk.rd, h1, bR, e0, hlen], by rw [hk.wr, h2, e3], by rw [e3, bR, e0, ← hlen]; exact h3, h5⟩
  refine WP.mono (loop_ok hp) fun s' ⟨r, wr, sp, e⟩ => ⟨by rw [r, hk.rd], by rw [wr, hk.wr],
    by rw [sp, hk.sp], ?_⟩
  show PolyIs s'.mem (s₀.gpr .x3) (decodeDecompress ((s₀.gpr .x2).setWidth 32).toNat
    (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
  rw [hlen, hdd, ← e3, ← e0, ← hm]
  exact e

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  have hd' := mem_widths hd
  suffices h : WP isa decodeDecompress s fun s' => s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_movImm fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x5, .x9] s s₂ := (h₁.keep.trans h₂.keep).mono
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x5 : (s₂.gpr .x5).toNat = q := by rw [h₂.get .x5, e₁]; rfl
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 160)) := by
    rw [eval_zero, eq_zero_iff, e₂, h₁.get .x1, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases hd' with h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 5 := by simp at hb; omega
    exact WP.mono (width_ok (.inl rfl) hs e k₂ m₂ x5) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  · have e : ((s.gpr .x2).setWidth 32).toNat = 11 := by
      simp at hb
      rcases hd' with h | h <;> rw [h] at hlen <;> omega
    exact WP.mono (width_ok (.inr rfl) hs e k₂ m₂ x5) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩

theorem ct : ConstantTime isa decodeDecompressAArch64.pre decodeDecompressAArch64.pub
    decodeDecompress :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x3])
    (fun _ _ _ _ ⟨h0, h1, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 160 | .x2 => 5 | .x3 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress_verified :
    Verified AArch64.target decodeDecompress (Spec.MlKem1024.decodeDecompressContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig,
      decodeDecompressAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.DD
