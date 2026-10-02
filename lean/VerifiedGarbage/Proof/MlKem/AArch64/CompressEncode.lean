import VerifiedGarbage.Proof.MlKem.AArch64.Width
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on AArch64: `ceLoop`, one width of `vg_mlkem_compress_encode`

Group `g` of the output is the number whose base-`2ᵈ` digits are the
compressed coefficients `c g … c g + c - 1` (`byteEncode_group`): `acc g c`,
built digit by digit (`coeff_step`) and stored byte by byte (`byte_step`).
-/

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (w : Width) (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev oP : Addr := s₀.gpr .x2
abbrev oR : Region := ⟨oP s₀, 32 * w.d⟩
abbrev P : Poly := polyAt s₀.mem (fP s₀)
/-- Coefficient `i`, compressed. -/
def C (i : Nat) : Nat := compress w.d (P s₀)[i]!
/-- Byte `j` of the output. -/
def L (j : Nat) : Byte := (compressEncode w.d (P s₀))[j]!
/-- The first `e` compressed coefficients of group `g`, as the digits of a number. -/
def acc (g e : Nat) : Nat := digits w.d ((List.range e).map fun e' => C w s₀ (w.c * g + e'))
/-- The output's bytes before. -/
def old (j : Nat) : Byte := s₀.mem (oP s₀ + BitVec.ofNat 64 j)

end

structure Pre (w : Width) (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀)]
  wr : s₀.wr = [oR w s₀]
  disj : (polyRegion (fP s₀)).Disjoint (oR w s₀)
  red : Reduced s₀.mem (fP s₀)
  x6 : (s₀.gpr .x6).toNat = 262080

/-- After `g` groups. -/
structure Inv (w : Width) (s₀ : State) (g : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀ + BitVec.ofNat 64 (4 * w.c * g)
  x2 : s.gpr .x2 = oP s₀ + BitVec.ofNat 64 (w.nb * g)
  x5 : (s.gpr .x5).toNat = w.mul
  x6 : (s.gpr .x6).toNat = 262080
  x7 : (s.gpr .x7).toNat = 2 ^ w.d - 1
  x11 : (s.gpr .x11).toNat = 256 / w.c - g
  out : BytesUpTo s.mem (oP s₀) (32 * w.d) (w.nb * g) (L w s₀) (old s₀)
  frame : Frame [oR w s₀] s₀.mem s.mem

theorem C_lt (w : Width) (s₀ : State) (i : Nat) : C w s₀ i < 2 ^ w.d := compress_lt _ _

theorem acc_succ (w : Width) (s₀ : State) (g e : Nat) :
    acc w s₀ g (e + 1) = acc w s₀ g e + 2 ^ (w.d * e) * C w s₀ (w.c * g + e) :=
  digits_range_succ _ _ _

theorem acc_lt (w : Width) (s₀ : State) (g e : Nat) : acc w s₀ g e < 2 ^ (w.d * e) :=
  digits_range_lt (fun _ => C_lt _ _ _) _

/-- Byte `j` of group `g` of the output. -/
theorem L_eq {w : Width} (hw : WOk w) (s₀ : State) {g j : Nat} (hg : g < 256 / w.c) (hj : j < w.nb) :
    L w s₀ (w.nb * g + j) = BitVec.ofNat 8 (acc w s₀ g w.c / 2 ^ (8 * j)) := by
  have hcg : w.c * g + w.c ≤ 256 := by
    have := hw.cG
    have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at this
    omega
  have hk : w.nb * g + j < 32 * w.d := by
    have := hw.bytes
    have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at this
    omega
  rw [L, Spec.MlKem.compressEncode, byteEncode_group hw.d_pos hw.dc (map_toList_lt _ (compress_lt w.d)) hj hk,
    take_drop_eq _ 0 (by rw [map_toList_length]; exact hcg), acc]
  refine congrArg (fun x => BitVec.ofNat 8 (digits w.d x / 2 ^ (8 * j))) (List.map_congr_left ?_)
  intro e he
  rw [map_toList_getD _ _ (by have := List.mem_range.mp he; omega)]
  rfl

theorem Pre.coeff {w : Width} {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [oR w s₀] s₀.mem m) {i : Nat} (hi : i < 256) :
    (coeffAt m (fP s₀) i).toNat = ((P s₀)[i]!).val := by
  rw [coeffAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hi,
    polyAt_val hp.red (show i < n from hi)]

/-- Compressing coefficient `e` of group `g` into `x9`. -/
theorem coeff_step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat}
    (hg : g < 256 / w.c) {s : State} (h : Inv w s₀ g s) (e : Nat) (he : e < w.c) (t : State)
    (ht : Only [.x9, .x10] s t ∧ (t.gpr .x9).toNat = acc w s₀ g e) :
    WP isa (.block (ceCoeff w e)) t fun t' =>
      Only [.x9, .x10] s t' ∧ (t'.gpr .x9).toNat = acc w s₀ g (e + 1) := by
  obtain ⟨ht, h9⟩ := ht
  have hcg : w.c * g + e < 256 := by
    have := hw.cG
    have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
    rw [Nat.mul_succ] at this
    omega
  have hq : q = 3329 := rfl
  have hle := hw.c_le
  have hd := hw.d_le
  have hde1 : w.d * (e + 1) ≤ 40 := by
    have := Nat.mul_le_mul_left w.d (show e + 1 ≤ w.c by omega)
    have := hw.dc
    have := hw.nb_le
    omega
  have hde : w.d * e ≤ 40 := Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hde1
  refine wp_ldrw (a := coeffAddr (fP s₀) (w.c * g + e)) ⟨by omega, by omega⟩ ?_ ?_ fun t₁ h₁ e₁ => ?_
  · rw [ht.get .x0, h.x0, ptr_add, coeffAddr, Nat.mul_add, Nat.mul_assoc]
  · rw [ht.rd, ht.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (coeff_contains _ (show _ < n from hcg)))
  have va : (t₁.gpr .x10).toNat = ((P s₀)[w.c * g + e]!).val := by
    rw [e₁, toNat_readW32, ← coeffAt_eq, ht.mem, hp.coeff h.frame hcg]
  have la := val_lt (P s₀)[w.c * g + e]!
  have harg := compress_arg_lt hw.mem (P s₀)[w.c * g + e]!
  have hmul : w.mul = compressMul w.d := hw.mul
  have x5 : (t₁.gpr .x5).toNat = compressMul w.d := by rw [h₁.get .x5, ht.get .x5, h.x5, hmul]
  have x6 : ∀ {u : State}, u.gpr .x6 = s.gpr .x6 → (u.gpr .x6).toNat = compressAdd := fun e =>
    by rw [e, h.x6]; rfl
  have x7 : ∀ {u : State}, u.gpr .x7 = s.gpr .x7 → (u.gpr .x7).toNat = 2 ^ w.d - 1 := fun e =>
    by rw [e, h.x7]
  refine wp_mul fun t₂ h₂ e₂ => wp_add fun t₃ h₃ e₃ => wp_lsr (by decide) fun t₄ h₄ e₄ =>
    wp_and fun t₅ h₅ e₅ => wp_lsl (by omega) fun t₆ h₆ e₆ => wp_add fun t₇ h₇ e₇ => wp_nil ?_
  have v₂ : (t₂.gpr .x10).toNat = ((P s₀)[w.c * g + e]!).val * compressMul w.d := by
    rw [e₂, toNat_mul_n (by rw [va, x5]; omega), va, x5]
  have v₃ : (t₃.gpr .x10).toNat = ((P s₀)[w.c * g + e]!).val * compressMul w.d + compressAdd := by
    rw [e₃, toNat_add_n (by rw [v₂, x6 (((ht.keep.trans h₁.keep).trans h₂.keep).get .x6)]; omega), v₂,
      x6 (((ht.keep.trans h₁.keep).trans h₂.keep).get .x6)]
  have v₅ : (t₅.gpr .x10).toNat = C w s₀ (w.c * g + e) := by
    rw [e₅, toNat_and_mask _ _ (x7 ((((ht.keep.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans
      h₄.keep |>.get .x7)), e₄, toNat_lsr, v₃, C, compress_eq hw.mem]
  have hC := C_lt w s₀ (w.c * g + e)
  have hpow : 2 ^ w.d * 2 ^ (w.d * e) ≤ 2 ^ 40 := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ] at hde1; omega)
  have hlt : C w s₀ (w.c * g + e) * 2 ^ (w.d * e) < 2 ^ 40 := by
    calc C w s₀ (w.c * g + e) * 2 ^ (w.d * e) < 2 ^ w.d * 2 ^ (w.d * e) :=
          Nat.mul_lt_mul_of_pos_right hC (Nat.two_pow_pos _)
      _ ≤ 2 ^ 40 := hpow
  have v₆ : (t₆.gpr .x10).toNat = C w s₀ (w.c * g + e) * 2 ^ (w.d * e) := by
    rw [e₆, toNat_lsl_n (by rw [v₅]; omega), v₅]
  have hacc := acc_lt w s₀ g e
  have v₉ : (t₆.gpr .x9).toNat = acc w s₀ g e := by
    rw [h₆.get .x9, h₅.get .x9, h₄.get .x9, h₃.get .x9, h₂.get .x9, h₁.get .x9, h9]
  refine ⟨(((((((ht.trans h₁).trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono, ?_⟩
  have : 2 ^ (w.d * e) ≤ 2 ^ 40 := Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpow
  rw [e₇, toNat_add_n (by rw [v₉, v₆]; omega), v₉, v₆, acc_succ, Nat.mul_comm (2 ^ (w.d * e))]

/-- During the bytes of group `g`, after `j` of them. -/
structure BInv (w : Width) (s₀ : State) (g : Nat) (s : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = acc w s₀ g w.c
  out : BytesUpTo t.mem (oP s₀) (32 * w.d) (w.nb * g + j) (L w s₀) (old s₀)
  frame : Frame [oR w s₀] s₀.mem t.mem

theorem nb_g_lt {w : Width} (hw : WOk w) {g j : Nat} (hg : g < 256 / w.c) (hj : j < w.nb) :
    w.nb * g + j < 32 * w.d := by
  have := hw.bytes
  have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

/-- Storing byte `j` of group `g`. -/
theorem byte_step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat}
    (hg : g < 256 / w.c) {s : State} (h : Inv w s₀ g s) (j : Nat) (hj : j < w.nb) (t : State)
    (ht : BInv w s₀ g s j t) :
    WP isa (.block (ceByte j)) t (BInv w s₀ g s (j + 1)) := by
  have hk := nb_g_lt hw hg hj
  have hd := hw.d_le
  have hn := hw.nb_le
  refine wp_lsr (by omega) fun t₁ h₁ e₁ => ?_
  refine wp_strb (a := oP s₀ + BitVec.ofNat 64 (w.nb * g + j)) (by omega)
    (by rw [h₁.get .x2, ht.keep.get .x2, h.x2, ptr_add]) ?_ fun t₂ h₂ => wp_nil ?_
  · rw [h₁.wr, ht.keep.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by omega))
  have hb : (t₁.gpr .x10).setWidth 8 = L w s₀ (w.nb * g + j) := by
    rw [setWidth8_of_toNat (n := acc w s₀ g w.c / 2 ^ (8 * j)) (by rw [e₁, toNat_lsr, ht.x9]),
      L_eq hw s₀ hg hj]
  refine ⟨(ht.keep.trans (h₁.keep.trans h₂.keep)).mono, by rw [h₂.gpr, h₁.get .x9, ht.x9], ?_, ?_⟩
  · rw [h₂.mem, h₁.mem, show w.nb * g + (j + 1) = w.nb * g + j + 1 by omega]
    rw [hb]
    exact ht.out.write (by omega) hk rfl
  · rw [h₂.mem, h₁.mem]
    exact ht.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem ceBody_eq (w : Width) : ceBody w = .movz .x .x9 0 0 :: ((List.range w.c).flatMap (ceCoeff w) ++
    ((List.range w.nb).flatMap ceByte ++
      ([.addImm .x .x0 .x0 (4 * w.c), .addImm .x .x2 .x2 w.nb, .subImm .x .x11 .x11 1] : List Instr))) := by
  simp only [ceBody, List.cons_append, List.append_assoc]

/-- One group. -/
theorem step {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {g : Nat} (hg : g < 256 / w.c)
    {s : State} (h : Inv w s₀ g s) :
    WP isa (.block (ceBody w)) s fun s' =>
      Inv w s₀ (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / w.c) := by
  have hc := hw.c_le
  have hn := hw.nb_le
  rw [ceBody_eq]
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun e t => Only [.x9, .x10] s t ∧ (t.gpr .x9).toNat = acc w s₀ g e)
    (fun e t he ht => coeff_step hw hp hg h e he t ht) w.c (Nat.le_refl _) s₁
    ⟨h₁.mono, by rw [e₁, toNat_imm]; rfl⟩) fun s₂ ⟨h₂, v₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (BInv w s₀ g s)
    (fun j t hj ht => byte_step hw hp hg h j hj t ht) w.nb (Nat.le_refl _) s₂
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
  · rw [h₆.get .x2, e₅, h₄.get .x2, h₃.keep.get .x2, h.x2, ptr_next]
  · rw [h₆.mem, h₅.mem, h₄.mem, Nat.mul_succ]
    exact h₃.out
  · rw [h₆.mem, h₅.mem, h₄.mem]
    exact h₃.frame

/-- The loop: `ByteEncode_d(Compress_d(f))` into the output. -/
theorem loop_ok {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) :
    WP isa (ceLoop w) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * w.d) = Spec.MlKem.compressEncode w.d (P s₀) := by
  have hG := hw.G_pos
  have hG' := hw.G_le
  refine WP.seq ?_
  rw [List.append_assoc, ← List.append_nil (movImm Reg.x11 _)]
  refine wp_movImm fun s₁ h₁ e₁ => wp_movImm fun s₂ h₂ e₂ => wp_movImm fun s₃ h₃ e₃ => wp_nil ?_
  refine WP.mono (count_loop hG (Inv w s₀) (fun g hg s h => step hw hp hg h) ?_)
    fun s' h => ⟨h.rd, h.wr, h.sp, (show BytesUpTo _ _ _ (32 * w.d) _ _ from hw.bytes ▸ h.out).eq
      (compressEncode_length _ _) fun _ _ => rfl⟩
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s₀.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have p5 : w.mul < 2 ^ 64 := by rw [hw.mul]; unfold compressMul; split <;> [decide; split <;> decide]
  have p7 : 2 ^ w.d - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw.d_le
    omega
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₃.get .x2, Nat.mul_zero, ptr_zero],
    by rw [h₃.get .x5, h₂.get .x5, e₁, toNat_ofNat_lt p5],
    by rw [k₃.get .x6, hp.x6], by rw [h₃.get .x7, e₂, toNat_ofNat_lt p7],
    by rw [e₃, toNat_ofNat_lt (by omega)]; simp, ?_, ?_⟩
  · rw [m₃, Nat.mul_zero]; exact BytesUpTo.zero _
  · rw [m₃]; exact Frame.refl _ _

end VG.Proof.MlKem.AArch64.CE

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_compress_encode(f = x0, d = w1, out = x2,
len = x3)`: if `d` is 1, 4 or 10, `len = 32 d` and the polynomial at `f` is
reduced, writes `ByteEncode_d(Compress_d(f))` to the `len` bytes at `out`. The
code may read `f` and write `out`, which do not overlap. -/
def compressEncodeAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    ((s.gpr .x1).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x3).toNat = 32 * ((s.gpr .x1).setWidth 32).toNat ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    compressEncode ((s.gpr .x1).setWidth 32).toNat (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} (hw : WOk w) {s₀ s : State} (hs : compressEncodeAArch64.pre s₀)
    (hd : ((s₀.gpr .x1).setWidth 32).toNat = w.d) (hk : Keep [.x6, .x9] s₀ s) (hm : s.mem = s₀.mem)
    (h6 : (s.gpr .x6).toNat = 262080) :
    WP isa (ceLoop w) s fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      compressEncodeAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, h5, h6'⟩ := hs
  rw [hd] at h5
  have e0 : fP s = s₀.gpr .x0 := hk.get .x0
  have e2 : oP s = s₀.gpr .x2 := hk.get .x2
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, e0], by rw [hk.wr, h2, oR, e2, h5], by rw [e0, oR, e2, ← h5]; exact h3,
      by rw [hm, e0]; exact h6', h6⟩
  refine WP.mono (loop_ok hw hp) fun s' ⟨r, wr, sp, e⟩ => ⟨by rw [r, hk.rd], by rw [wr, hk.wr],
    by rw [sp, hk.sp], ?_⟩
  show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
  rw [h5, hd, ← hk.get .x2, e, P, fP, hm, hk.get .x0]

theorem correct (s : State) (hs : compressEncodeAArch64.pre s) :
    ∃ t s', Exec isa compressEncode s t s' ∧ abiPreserved s s' ∧ compressEncodeAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen, -⟩ := hs'
  suffices h : WP isa compressEncode s fun s' => s'.sp = s.sp ∧ compressEncodeAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_movImm fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x6, .x9] s s₂ := (h₁.keep.trans h₂.keep).mono
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x6 : (s₂.gpr .x6).toNat = 262080 := by rw [h₂.get .x6, e₁]; rfl
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x3).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, h₁.get .x3, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 1 := by simp at hb; omega
    exact WP.mono (width_ok width1_ok hs e k₂ m₂ x6) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x6, .x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x3).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x3, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 4 := by simp at hb'; omega
    exact WP.mono (width_ok width4_ok hs e k₃ (by rw [h₃.mem, m₂]) (by rw [h₃.get .x6, x6]))
      fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  · have e : ((s.gpr .x1).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact WP.mono (width_ok width10_ok hs e k₃ (by rw [h₃.mem, m₂]) (by rw [h₃.get .x6, x6]))
      fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩

theorem ct : ConstantTime isa compressEncodeAArch64.pre compressEncodeAArch64.pub compressEncode :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 4 | .x2 => 0x2000 | .x3 => 128 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem compressEncode_verified :
    Verified AArch64.target compressEncode (Spec.MlKem.compressEncodeContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig,
      compressEncodeAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.CE
