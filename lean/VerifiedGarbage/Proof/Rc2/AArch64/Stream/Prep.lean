import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Copy

/-!
# Streaming RC2-CBC on AArch64: the copies before CBC

With complete blocks, the update copies the `p` pending bytes and the first
`out_len - p` bytes of data to `out`, and the rest of the data to `ctx + 136`,
then sets up the CBC call's arguments (`prep_ok`).
-/

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (copy toOut toOutData toPending cbcArgs prep)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_add wp_sub wp_lsr toNat_ofNat_lt sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_frame)

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem inR {rs : List Region} {R : Region} {a : Addr} {n : Nat} (hR : R ∈ rs) (hc : R.Contains a n) :
    InRegions rs a n := ⟨R, hR, hc⟩

theorem shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The arguments of an update, and their regions. -/
structure Lay (σ : State) (c dp op b : Addr) (p len ol : Nat) : Prop where
  x0 : σ.gpr .x0 = c
  x1 : σ.gpr .x1 = BitVec.ofNat 64 p
  x2 : σ.gpr .x2 = dp
  x3 : σ.gpr .x3 = BitVec.ofNat 64 len
  x4 : σ.gpr .x4 = op
  x5 : σ.gpr .x5 = BitVec.ofNat 64 ol
  x6 : σ.gpr .x6 = b
  rd : σ.rd = [⟨dp, len⟩]
  wr : σ.wr = [⟨c, 144⟩, ⟨op, ol⟩, ⟨b, 576⟩]
  cd : Region.Disjoint ⟨c, 144⟩ ⟨dp, len⟩
  co : Region.Disjoint ⟨c, 144⟩ ⟨op, ol⟩
  cb : Region.Disjoint ⟨c, 144⟩ ⟨b, 576⟩
  dout : Region.Disjoint ⟨dp, len⟩ ⟨op, ol⟩
  db : Region.Disjoint ⟨dp, len⟩ ⟨b, 576⟩
  ob : Region.Disjoint ⟨op, ol⟩ ⟨b, 576⟩
  fo : op.toNat + ol ≤ 2 ^ 64
  lenlt : len < 2 ^ 64
  ollt : ol < 2 ^ 64
  p8 : p < 8
  olq : ol = (p + len) / 8 * 8

/-- What the copies leave, for the CBC call. -/
structure CallSt (σ : State) (c dp op b : Addr) (p len ol : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = c
  x1 : s.gpr .x1 = c + BitVec.ofNat 64 128
  x2 : s.gpr .x2 = op
  x3 : s.gpr .x3 = BitVec.ofNat 64 ((p + len) / 8)
  x4 : s.gpr .x4 = b
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  out : Spec.Rc2.bytesAt s.mem op ol =
    Spec.Rc2.bytesAt σ.mem (c + BitVec.ofNat 64 136) p ++ Spec.Rc2.bytesAt σ.mem dp (ol - p)
  frame : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] σ.mem s.mem
  pend : Spec.Rc2.bytesAt s.mem (c + BitVec.ofNat 64 136) (len + p - ol) =
    Spec.Rc2.bytesAt σ.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol)

theorem bytesAt_writeBytes' (m : Mem) (q src : Addr) (k : Nat) (hk : k ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m q (Spec.Rc2.bytesAt m src k)) q k = Spec.Rc2.bytesAt m src k := by
  have h := bytesAt_writeBytes m q (Spec.Rc2.bytesAt m src k) (by rw [bytesAt_length]; exact hk)
  rwa [bytesAt_length] at h

theorem frame_writeBytes (m : Mem) (q src : Addr) (k : Nat) :
    Frame [⟨q, k⟩] m (writeBytes m q (Spec.Rc2.bytesAt m src k)) :=
  writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

theorem prep_ok {σ : State} {c dp op b : Addr} {p len ol : Nat} (h : Lay σ c dp op b p len ol)
    (hol : ol ≠ 0) :
    WP isa prep σ (CallSt σ c dp op b p len ol) := by
  unfold prep
  have p8 := h.p8
  have olq := h.olq
  have fo := h.fo
  have hl := h.lenlt
  have hpo : p ≤ ol := by omega
  have hol8 : 8 ≤ ol := by omega
  have hrl : ol - p ≤ len := by omega
  have hr8 : len + p - ol < 8 := by omega
  have hc136 : ∀ i, i < 8 → InRegions σ.wr (c + BitVec.ofNat 64 136 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [h.wr, Offset.add_add]
    exact inR (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have hctxSub : Region.Sub ⟨c + BitVec.ofNat 64 136, 8⟩ ⟨c, 144⟩ := Offset.sub_base _ (by omega)
  -- `toOut`, and the pending bytes to `out`.
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have g₃ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₃.gpr r = σ.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine WP.seq (copy_ok (A := c + BitVec.ofNat 64 136) (B := op) (k := p) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x0])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x4]; simp)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.x1]) (by omega)
    (fun i hi => by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      obtain ⟨R, hR, hc⟩ := hc136 i (by omega)
      exact ⟨R, List.mem_append_right _ hR, hc⟩)
    (fun i hi => by
      rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
      exact inR (R := ⟨op, ol⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    ((h.co.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hpo))
    fun s₄ c₄ => ?_)
  have m₄ : s₄.mem = writeBytes σ.mem op (Spec.Rc2.bytesAt σ.mem (c + BitVec.ofNat 64 136) p) := by
    rw [c₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₄.gpr r = σ.gpr r :=
    fun r h0 h1 h2 h3 => by rw [c₄.other r h0 h1 h2 h3, g₃ r h1 h2 h3]
  have x11₄ : s₄.gpr .x11 = op + BitVec.ofNat 64 p := by rw [c₄.pdst, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x4]
  -- The first `ol - p` bytes of data after them.
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hd₄ : Spec.Rc2.bytesAt s₄.mem dp (ol - p) = Spec.Rc2.bytesAt σ.mem dp (ol - p) := by
    rw [m₄]
    exact Proof.Rc2.bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨op, ol⟩) (by
      rw [bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))
      _ _ (by omega) (by simpa using (h.dout.sub_left (Region.sub_prefix hrl)))
  refine WP.seq (copy_ok (A := dp) (B := op + BitVec.ofNat 64 p) (k := ol - p) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), h.x2]; simp)
    (by rw [u₅.other _ (by decide), x11₄]; simp)
    (by rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₄ _ (by decide) (by decide) (by decide) (by decide), h.x5, h.x1, sub_ofNat hpo]) (by omega)
    (fun i hi => by
      rw [u₅.rd, u₅.wr, c₄.rd, c₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd]
      exact inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₅.wr, c₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, Offset.add_add]
      exact inR (R := ⟨op, ol⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    ((h.dout.sub_left (Region.sub_prefix hrl)).sub_right (Offset.sub_base _ (by omega)))
    fun s₆ c₆ => ?_)
  have m₆ : s₆.mem = writeBytes s₄.mem (op + BitVec.ofNat 64 p) (Spec.Rc2.bytesAt s₄.mem dp (ol - p)) := by
    rw [c₆.mem, u₅.mem]
  have x2₆ : s₆.gpr .x2 = dp + BitVec.ofNat 64 (ol - p) := by
    rw [c₆.psrc, u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), h.x2]
  have g₆ : ∀ r, r ≠ .x9 → r ≠ .x2 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s₆.gpr r = σ.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [c₆.other r h0 h1 h3 h4, u₅.other r h4, g₄ r h0 h2 h3 h4]
  -- The rest of the data to `ctx + 136`.
  refine WP.seq (wp_add fun s₇ u₇ => wp_sub fun s₈ u₈ => wp_mov fun s₉ u₉ => WP.block_nil ?_)
  have hp₆ : Spec.Rc2.bytesAt s₆.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol) =
      Spec.Rc2.bytesAt σ.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol) := by
    have hs : Region.Sub ⟨dp + BitVec.ofNat 64 (ol - p), len + p - ol⟩ ⟨dp, len⟩ :=
      Offset.sub_base _ (by omega)
    rw [m₆, Proof.Rc2.bytesAt_frame (frame_writeBytes _ _ _ _) _ _ (by omega)
      (by simpa using (h.dout.sub_left hs).sub_right (Offset.sub_base _ (by omega))), m₄,
      Proof.Rc2.bytesAt_frame (frame_writeBytes _ _ _ _) _ _ (by omega)
      (by simpa using (h.dout.sub_left hs).sub_right (Region.sub_prefix hpo))]
  refine WP.seq (copy_ok (A := dp + BitVec.ofNat 64 (ol - p)) (B := c + BitVec.ofNat 64 136)
    (k := len + p - ol) (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), x2₆]; simp)
    (by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x0])
    (by rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)
        (by decide), g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x3, h.x1, h.x5,
        BitVec.ofNat_add_ofNat, sub_ofNat (by omega)]) (by omega)
    (fun i hi => by
      rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, c₆.rd, c₆.wr, u₅.rd, u₅.wr, c₄.rd, c₄.wr, u₃.rd,
        u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, Offset.add_add]
      exact inR (R := ⟨dp, len⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (fun i hi => by
      rw [u₉.wr, u₈.wr, u₇.wr, c₆.wr, u₅.wr, c₄.wr, u₃.wr, u₂.wr, u₁.wr]
      exact hc136 i (by omega))
    (((h.cd.sub_left hctxSub).sub_left (Region.sub_prefix (by omega))).sub_right
      (Offset.sub_base _ (by omega)) |>.symm)
    fun s₁₀ c₁₀ => ?_)
  have g₁₀ : ∀ r, r ≠ .x9 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
      s₁₀.gpr r = σ.gpr r := fun r h0 h1 h2 h3 h4 h5 => by
    rw [c₁₀.other r h0 h1 h3 h2, u₉.other r h3, u₈.other r h2, u₇.other r h2, g₆ r h0 h1 h3 h4 h5]
  -- The arguments of the CBC function.
  refine wp_addImm (by decide) fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => wp_lsr (by decide) fun s₁₃ u₁₃ =>
    wp_mov fun s₁₄ u₁₄ => WP.block_nil ?_
  have hm₁₀ : s₁₀.mem = writeBytes s₆.mem (c + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt s₆.mem (dp + BitVec.ofNat 64 (ol - p)) (len + p - ol)) := by
    rw [c₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have hm : s₁₄.mem = s₁₀.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem]
  -- The frames of the three copies.
  have f₄ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] σ.mem s₄.mem := by
    rw [m₄]; exact (frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hpo⟩
  have f₆ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] s₄.mem s₆.mem := by
    rw [m₆]; exact (frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩
  have f₁₀ : Frame [⟨op, ol⟩, ⟨c + BitVec.ofNat 64 136, 8⟩] s₆.mem s₁₀.mem := by
    rw [hm₁₀]; exact (frame_writeBytes _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c + BitVec.ofNat 64 136, 8⟩, by simp, Region.sub_prefix (by omega)⟩
  have hoc : Region.Disjoint ⟨op, ol⟩ ⟨c + BitVec.ofNat 64 136, len + p - ol⟩ :=
    ((h.co.sub_left hctxSub).sub_left (Region.sub_prefix (by omega))).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.x0]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr,
      u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.x4]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x5,
      shr3 h.ollt, olq, Nat.mul_div_cancel _ (by decide)]
  · rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x6]
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, c₁₀.rd, u₉.rd, u₈.rd, u₇.rd, c₆.rd, u₅.rd, c₄.rd, u₃.rd,
      u₂.rd, u₁.rd]
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, c₁₀.wr, u₉.wr, u₈.wr, u₇.wr, c₆.wr, u₅.wr, c₄.wr, u₃.wr,
      u₂.wr, u₁.wr]
  · rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, c₁₀.sp, u₉.sp, u₈.sp, u₇.sp, c₆.sp, u₅.sp, c₄.sp, u₃.sp,
      u₂.sp, u₁.sp]
  · rw [hm, hm₁₀, Proof.Rc2.bytesAt_frame (frame_writeBytes _ _ _ _) _ _ (by omega) (by simpa using hoc),
      show ol = p + (ol - p) by omega, bytesAt_add, Nat.add_sub_cancel_left, m₆,
      Proof.Rc2.bytesAt_frame (frame_writeBytes _ _ _ _) _ _ (by omega)
        (by simpa using Offset.base_disjoint op (Nat.le_refl p) (by omega)),
      bytesAt_writeBytes' _ _ _ _ (by omega), hd₄, m₄, bytesAt_writeBytes' _ _ _ _ (by omega)]
  · rw [hm]; exact f₄.trans (f₆.trans f₁₀)
  · rw [hm, hm₁₀, bytesAt_writeBytes' _ _ _ _ (by omega), hp₆]

end VG.Proof.Rc2.AArch64.Stream
