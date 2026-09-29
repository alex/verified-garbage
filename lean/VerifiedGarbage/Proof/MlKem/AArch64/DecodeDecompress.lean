import VerifiedGarbage.Proof.MlKem.AArch64.Width
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on AArch64: `vg_mlkem_decode_decompress`

Untrusted: everything here is checked by Lean. Group `g` of the input is
the number whose bytes are its bytes (`num g nb`, built byte by byte,
`byte_step`), and coefficient `e` of the group is its base-`2ᵈ` digit `e`
(`byteDecode_group`), decompressed (`coeff_step`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem_decode_decompress(b = x0, len = x1, d = w2,
f = x3)`: if `d` is 1, 4 or 10 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`,
reduced. The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (w : Width) (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x3
abbrev bR : Region := ⟨bP s₀, 32 * w.d⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (32 * w.d)
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B w s₀).getD j 0).toNat
/-- The first `j` bytes of group `g`, as a little-endian number. -/
def num (g j : Nat) : Nat := digits 8 ((List.range j).map fun j' => byte w s₀ (w.nb * g + j'))
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress w.d (B w s₀))[i]!).val
/-- The output's coefficients before. -/
def old (i : Nat) : BitVec 32 := coeffAt s₀.mem (fP s₀) i

end

structure Pre (w : Width) (s₀ : State) : Prop where
  rd : s₀.rd = [bR w s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR w s₀).Disjoint (polyRegion (fP s₀))
  x5 : (s₀.gpr .x5).toNat = q

/-- After `g` groups. -/
structure Inv (w : Width) (s₀ : State) (g : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * g)
  x3 : s.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * w.c * g)
  x5 : (s.gpr .x5).toNat = q
  x6 : (s.gpr .x6).toNat = 2 ^ (w.d - 1)
  x7 : (s.gpr .x7).toNat = 2 ^ w.d - 1
  x11 : (s.gpr .x11).toNat = 256 / w.c - g
  out : CoeffsUpTo s.mem (fP s₀) (w.c * g) (G w s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

theorem num_succ (w : Width) (s₀ : State) (g j : Nat) :
    num w s₀ g (j + 1) = num w s₀ g j + 2 ^ (8 * j) * byte w s₀ (w.nb * g + j) :=
  digits_range_succ _ _ _

theorem num_lt (w : Width) (s₀ : State) (g j : Nat) : num w s₀ g j < 2 ^ (8 * j) :=
  digits_range_lt (fun _ => byte_lt _) _

theorem cg_lt {w : Width} (hw : WOk w) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    w.c * g + e < 256 := by
  have := hw.cG
  have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

theorem nbg_le {w : Width} (hw : WOk w) {g : Nat} (hg : g < 256 / w.c) :
    w.nb * g + w.nb ≤ 32 * w.d := by
  have := hw.bytes
  have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

/-- Coefficient `e` of group `g` of the output. -/
theorem G_eq {w : Width} (hw : WOk w) (s₀ : State) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    G w s₀ (w.c * g + e) =
      BitVec.ofNat 32 ((q * (num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d) + 2 ^ (w.d - 1)) / 2 ^ w.d) := by
  have hi := cg_lt hw hg he
  have hd12 : w.d < 12 := by have := hw.d_le; omega
  rw [G, decodeDecompress_get _ _ (show _ < n from hi),
    byteDecode_group hw.dc _ he (show _ < n from hi), bytes_map_take_drop _ (by
      rw [bytesAt_length]; exact nbg_le hw hg), ite_eq_left hd12, Nat.mod_mod,
    (decompress_val hw.mem (Nat.mod_lt _ (Nat.two_pow_pos _))).1]
  rfl

theorem Pre.byte_eq {w : Width} {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {j : Nat} (hj : j < 32 * w.d) (hw : w.d ≤ 10) :
    (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte w s₀ j := by
  rw [byte_frame (len := 32 * w.d) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by omega) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) (32 * w.d)).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

/-- Byte `j` of group `g` into `x9`. -/
theorem byte_step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat}
    (hg : g < 256 / w.c) {s : State} (h : Inv w s₀ g s) (j : Nat) (hj : j < w.nb) (t : State)
    (ht : Only [.x9, .x10] s t ∧ (t.gpr .x9).toNat = num w s₀ g j) :
    WP isa (.block (ddByte j)) t fun t' =>
      Only [.x9, .x10] s t' ∧ (t'.gpr .x9).toNat = num w s₀ g (j + 1) := by
  obtain ⟨ht, h9⟩ := ht
  have hk := nbg_le hw hg
  have hn := hw.nb_le
  have hd := hw.d_le
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 (w.nb * g + j)) (by omega)
    (by rw [ht.get .x0, h.x0, ptr_add]) ?_ fun t₁ h₁ e₁ => ?_
  · rw [ht.rd, ht.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by omega)))
  have v₁ : (t₁.gpr .x10).toNat = byte w s₀ (w.nb * g + j) := by
    rw [e₁, toNat_byte, ht.mem, hp.byte_eq h.frame (by omega) hd]
  have hb := byte_lt ((B w s₀).getD (w.nb * g + j) 0)
  have hpow : 2 ^ 8 * 2 ^ (8 * j) ≤ 2 ^ 40 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : byte w s₀ (w.nb * g + j) * 2 ^ (8 * j) < 2 ^ 40 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)) hpow
  refine wp_lsl (by omega) fun t₂ h₂ e₂ => wp_add fun t₃ h₃ e₃ => wp_nil ?_
  have v₂ : (t₂.gpr .x10).toNat = byte w s₀ (w.nb * g + j) * 2 ^ (8 * j) := by
    rw [e₂, toNat_lsl_n (by rw [v₁]; omega), v₁]
  have hnum := num_lt w s₀ g j
  have : 2 ^ (8 * j) ≤ 2 ^ 40 := Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpow
  refine ⟨((ht.trans h₁).trans (h₂.trans h₃)).mono, ?_⟩
  rw [e₃, h₂.get .x9, h₁.get .x9, toNat_add_n (by rw [h9, v₂]; omega), h9, v₂, num_succ,
    Nat.mul_comm (2 ^ (8 * j))]

/-- During the coefficients of group `g`, after `e` of them. -/
structure CInv (w : Width) (s₀ : State) (g : Nat) (s : State) (e : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = num w s₀ g w.nb
  out : CoeffsUpTo t.mem (fP s₀) (w.c * g + e) (G w s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem t.mem

/-- Coefficient `e` of group `g`. -/
theorem coeff_step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat}
    (hg : g < 256 / w.c) {s : State} (h : Inv w s₀ g s) (e : Nat) (he : e < w.c) (t : State)
    (ht : CInv w s₀ g s e t) :
    WP isa (.block (ddCoeff w e)) t (CInv w s₀ g s (e + 1)) := by
  have hi := cg_lt hw hg he
  have hd := hw.d_le
  have hc := hw.c_le
  have hq : q = 3329 := rfl
  have hde : w.d * e ≤ 40 := by
    have := Nat.mul_le_mul_left w.d (show e ≤ w.c by omega)
    have := hw.dc
    have := hw.nb_le
    omega
  refine wp_lsr (by omega) fun t₁ h₁ e₁ => wp_and fun t₂ h₂ e₂ => wp_mul fun t₃ h₃ e₃ =>
    wp_add fun t₄ h₄ e₄ => wp_lsr (by omega) fun t₅ h₅ e₅ => ?_
  have k₅ := ((((ht.keep.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep
  have y : (t₂.gpr .x10).toNat = num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d := by
    rw [e₂, toNat_and_mask _ _ (by rw [h₁.get .x7, ht.keep.get .x7, h.x7]), e₁, toNat_lsr, ht.x9]
  have hy : num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d < 2 ^ 10 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hd)
  have h6 : 2 ^ (w.d - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  have hyq : num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d * q < 2 ^ 22 := by rw [hq]; omega
  have v₃ : (t₃.gpr .x10).toNat = num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d * q := by
    rw [e₃, toNat_mul_n (by rw [y, h₂.get .x5, h₁.get .x5, ht.keep.get .x5, h.x5]; omega), y,
      h₂.get .x5, h₁.get .x5, ht.keep.get .x5, h.x5]
  have v₄ : (t₄.gpr .x10).toNat = num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d * q + 2 ^ (w.d - 1) := by
    have x6 : (t₃.gpr .x6).toNat = 2 ^ (w.d - 1) := by
      rw [h₃.get .x6, h₂.get .x6, h₁.get .x6, ht.keep.get .x6, h.x6]
    have hb4 : num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d * q + 2 ^ (w.d - 1) < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hyq h6) (by decide)
    rw [e₄, toNat_add_n (by rw [v₃, x6]; exact hb4), v₃, x6]
  refine wp_strw (a := coeffAddr (fP s₀) (w.c * g + e)) ⟨by omega, by omega⟩ ?_ ?_ fun t₆ h₆ => wp_nil ?_
  · rw [k₅.get .x3, h.x3, ptr_add, coeffAddr, Nat.mul_add, Nat.mul_assoc]
  · rw [k₅.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (coeff_contains _ (show _ < n from hi))
  have v₅ : (t₅.gpr .x10).setWidth 32 = G w s₀ (w.c * g + e) := by
    rw [setWidth32_of_toNat (by rw [e₅, toNat_lsr, v₄]), G_eq hw s₀ hg he, Nat.mul_comm q]
  refine ⟨(k₅.trans h₆.keep).mono, by
    rw [h₆.gpr, h₅.get .x9, h₄.get .x9, h₃.get .x9, h₂.get .x9, h₁.get .x9]; exact ht.x9, ?_, ?_⟩
  · rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, v₅]
    exact ht.out.write (by omega) rfl
  · rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    exact ht.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show _ < n from hi))

theorem ddBody_eq (w : Width) : ddBody w = .movz .x .x9 0 0 :: ((List.range w.nb).flatMap ddByte ++
    ((List.range w.c).flatMap (ddCoeff w) ++
      ([.addImm .x .x0 .x0 w.nb, .addImm .x .x3 .x3 (4 * w.c), .subImm .x .x11 .x11 1] : List Instr))) := by
  simp only [ddBody, List.cons_append, List.append_assoc]

/-- One group. -/
theorem step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat} (hg : g < 256 / w.c)
    {s : State} (h : Inv w s₀ g s) :
    WP isa (.block (ddBody w)) s fun s' =>
      Inv w s₀ (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / w.c) := by
  have hc := hw.c_le
  have hn := hw.nb_le
  rw [ddBody_eq]
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun j t => Only [.x9, .x10] s t ∧ (t.gpr .x9).toNat = num w s₀ g j)
    (fun j t hj ht => byte_step hw hp hg h j hj t ht) w.nb (Nat.le_refl _) s₁
    ⟨h₁.mono, by rw [e₁, toNat_imm]; rfl⟩) fun s₂ ⟨h₂, v₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (CInv w s₀ g s)
    (fun e t he ht => coeff_step hw hp hg h e he t ht) w.c (Nat.le_refl _) s₂
    ⟨h₂.keep, v₂, by rw [h₂.mem, Nat.add_zero]; exact h.out, by rw [h₂.mem]; exact h.frame⟩)
    fun s₃ h₃ => ?_
  refine wp_addImm (by omega) fun s₄ h₄ e₄ => wp_addImm (by omega) fun s₅ h₅ e₅ =>
    wp_subImm (by decide) fun s₆ h₆ e₆ => wp_nil ?_
  have k₅ := (h₃.keep.trans h₄.keep).trans h₅.keep
  have c11 : (s₅.gpr .x11).toNat = 256 / w.c - g := by rw [k₅.get .x11, h.x11]
  have v11 : (s₆.gpr .x11).toNat = 256 / w.c - (g + 1) := by
    rw [e₆, toNat_sub_n (by rw [c11]; simp; omega), c11]
    simp
    omega
  have k₆ := k₅.trans h₆.keep
  refine ⟨⟨by rw [k₆.rd, h.rd], by rw [k₆.wr, h.wr], by rw [k₆.sp, h.sp], ?_, ?_,
    by rw [k₆.get .x5, h.x5], by rw [k₆.get .x6, h.x6], by rw [k₆.get .x7, h.x7], v11, ?_, ?_⟩,
    by rw [v11]; omega⟩
  · rw [h₆.get .x0, h₅.get .x0, e₄, h₃.keep.get .x0, h.x0, ptr_next]
  · rw [h₆.get .x3, e₅, h₄.get .x3, h₃.keep.get .x3, h.x3, ptr_next]
  · rw [h₆.mem, h₅.mem, h₄.mem, Nat.mul_succ]
    exact h₃.out
  · rw [h₆.mem, h₅.mem, h₄.mem]
    exact h₃.frame

/-- The loop: `Decompress_d(ByteDecode_d(B))` into the output. -/
theorem loop_ok {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) :
    WP isa (ddLoop w) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      PolyIs s'.mem (fP s₀) (decodeDecompress w.d (B w s₀)) := by
  have hG := hw.G_pos
  have hG' := hw.G_le
  refine WP.seq ?_
  rw [List.append_assoc, ← List.append_nil (movImm Reg.x11 _)]
  refine wp_movImm fun s₁ h₁ e₁ => wp_movImm fun s₂ h₂ e₂ => wp_movImm fun s₃ h₃ e₃ => wp_nil ?_
  refine WP.mono (count_loop hG (Inv w s₀) (fun g hg s h => step hw hp hg h) ?_)
    fun s' h => ⟨h.rd, h.wr, h.sp, (show CoeffsUpTo _ _ 256 _ _ from hw.cG ▸ h.out).polyIs
      fun _ _ => rfl⟩
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s₀.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have p6 : 2 ^ (w.d - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by have := hw.d_le; omega)
  have p7 : 2 ^ w.d - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw.d_le
    omega
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₃.get .x3, Nat.mul_zero, ptr_zero], by rw [k₃.get .x5, hp.x5],
    by rw [h₃.get .x6, h₂.get .x6, e₁, toNat_ofNat_lt p6], by rw [h₃.get .x7, e₂, toNat_ofNat_lt p7],
    by rw [e₃, toNat_ofNat_lt (by omega)]; simp, ?_, ?_⟩
  · rw [m₃, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · rw [m₃]; exact Frame.refl _ _

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} (hw : WOk w) {s₀ s : State} (hs : decodeDecompressAArch64.pre s₀)
    (hd : ((s₀.gpr .x2).setWidth 32).toNat = w.d) (hk : Keep [.x5, .x9] s₀ s) (hm : s.mem = s₀.mem)
    (h5 : (s.gpr .x5).toNat = q) :
    WP isa (ddLoop w) s fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      decodeDecompressAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, hlen⟩ := hs
  rw [hd] at hlen
  have e0 : bP s = s₀.gpr .x0 := hk.get .x0
  have e3 : fP s = s₀.gpr .x3 := hk.get .x3
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, bR, e0, hlen], by rw [hk.wr, h2, e3], by rw [e3, bR, e0, ← hlen]; exact h3, h5⟩
  refine WP.mono (loop_ok hw hp) fun s' ⟨r, wr, sp, e⟩ => ⟨by rw [r, hk.rd], by rw [wr, hk.wr],
    by rw [sp, hk.sp], ?_⟩
  show PolyIs s'.mem (s₀.gpr .x3) (decodeDecompress ((s₀.gpr .x2).setWidth 32).toNat
    (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
  rw [hlen, hd, ← e3, ← e0, ← hm]
  exact e

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  suffices h : WP isa decodeDecompress s fun s' => s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_movImm fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x5, .x9] s s₂ := (h₁.keep.trans h₂.keep).mono
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x5 : (s₂.gpr .x5).toNat = q := by rw [h₂.get .x5, e₁]; rfl
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, h₁.get .x1, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 1 := by simp at hb; omega
    exact WP.mono (width_ok width1_ok hs e k₂ m₂ x5) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x5, .x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x1).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x1, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 4 := by simp at hb'; omega
    exact WP.mono (width_ok width4_ok hs e k₃ (by rw [h₃.mem, m₂]) (by rw [h₃.get .x5, x5]))
      fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  · have e : ((s.gpr .x2).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact WP.mono (width_ok width10_ok hs e k₃ (by rw [h₃.mem, m₂]) (by rw [h₃.get .x5, x5]))
      fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩

theorem ct : ConstantTime isa decodeDecompressAArch64.pre decodeDecompressAArch64.pub
    decodeDecompress :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x3])
    (fun _ _ _ _ ⟨h0, h1, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 4 | .x3 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress_verified :
    Verified AArch64.target decodeDecompress (Spec.MlKem.decodeDecompressContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig,
      decodeDecompressAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.DD
