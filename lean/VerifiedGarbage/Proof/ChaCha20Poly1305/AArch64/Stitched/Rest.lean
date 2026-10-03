import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the rest of the data

`vg_chacha20_xor` (any backend) on the data after the chunks, from the
counter after them: the whole data encrypted from counter 1.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- The data after the chunks. -/
abbrev restR (s₀ : State) (T : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (512 * T), L s₀ - 512 * T⟩

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt; omega)

theorem not_rest {s₀ : State} {T k : Nat} (hk : k < 512 * T) (hT : 512 * T ≤ L s₀) :
    ¬ (restR s₀ T).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- The data from `512 T`, encrypted from the counter after `8 T` blocks. -/
theorem rest_call (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) {s w : State}
    {T : Nat} (hle : 512 * T ≤ L s₀)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T))
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hwr : w.wr = s₀.wr)
    (hcnt : stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (.call v.callee.name v.callee.code) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w s' ∧ Frame [sub s₀ 64 384, restR s₀ T] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ts : Region.Sub (restR s₀ T) (dR s₀) := Offset.sub_base _ (by omega)
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, restR s₀ T, ⟨off (cx s₀) 128, 320⟩] w.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [hwr, hp.wr], 64, rfl, by show 64 + 64 ≤ 1024; omega⟩
    · exact ⟨dR s₀, by simp [hwr, hp.wr], 512 * T, rfl, by show 512 * T + (L s₀ - 512 * T) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by simp [hwr, hp.wr], 128, rfl, by show 128 + 320 ≤ 1024; omega⟩
  refine xor_call v hx0 hx1 hx2 hx3 (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right ts)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left ts)
    (by have := hp.wrap_d; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (Covers.right hw) hw fun s' v' k' d' => ?_
  refine ⟨v', ?_, ?_, ?_⟩
  · refine k'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, ts⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨restR s₀ T, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < 512 * T
    · have hs : ¬ (⟨off (cx s₀) 64, 64⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)) _ hh (data_in hk)
      have hb : ¬ (⟨off (cx s₀) 128, 320⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)) _ hh (data_in hk)
      rw [k'.frame _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hs
        · exact not_rest hk' hle
        · exact hb), hdata k hk, ite_eq_left hk']
    · have ea : dp s₀ + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 (k - 512 * T) =
          dp s₀ + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      have x := VG.Proof.ChaCha20.AArch64.Mixed8.bytes_of_bytesAt
        (VG.Proof.ChaCha20.length_keystream _ _) d' (k := k - 512 * T) (by omega)
      rw [ea, hdata k hk, ite_eq_right hk', hcnt,
        VG.Proof.ChaCha20.keystream_getD _ (by omega)] at x
      rw [x, VG.Proof.ChaCha20.AArch64.Mixed8.ks_shift _ hk (t := T) (by omega)]

/-- The data before the rest is kept. -/
theorem prefix_rest {s₀ : State} (hp : APre s₀) {m m' : Mem} {T n : Nat}
    (hf : Frame [sub s₀ 64 384, restR s₀ T] m m') (hn : n ≤ 512 * T) (hT : 512 * T ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 384) (by lit_omega)) _ hh
      (data_in (by omega))
  · exact not_rest (by omega) hT

/-- `cryptRest`'s arguments: the stream's, from the context and `x22`, `x23`. -/
theorem restArgs_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128]) w
      fun w' => (w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
        w'.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w w') ∧
        ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23,
      .addImm .x .x3 .x21 128]) w fun w' =>
      w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
      w'.gpr .x3 = off (cx s₀) 128 ∧ w'.mem = w.mem ∧ w'.rd = w.rd ∧ w'.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
          by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.preservedV (WP.mono (WP.kept core (by simp [mov, dstOf, preserved]))
    fun w' ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩)

end VG.Proof.ChaCha20Poly1305.AArch64
