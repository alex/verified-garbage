import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.MacPad

/-!
# ChaCha20-Poly1305 on AArch64: the other parts

Untrusted: everything here is checked by Lean. The lengths block, the
encryption, absorbing the lengths, the tag, comparing tags, and restoring the
registers.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_mov wp_movz wp_sub wp_lsr wp_str wp_str32 wp_ldr
  stateAt_writeW_counter)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  intro x hx
  simp only [Region.Contains, off] at *
  have e : x - (cx s₀ + BitVec.ofNat 64 a) = (x - (cx s₀ + BitVec.ofNat 64 k)) + BitVec.ofNat 64 (k - a) := by
    rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega
  rw [e, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem mac_inv {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept (macR s₀) s s') : Inv s₀ s' :=
  h.step1 (k := 448) (n := 144) hk (by omega) (by omega) (by omega)

/-! ## The lengths block -/

theorem bytesAt_16 (m : Mem) (p : Addr) :
    bytesAt m p 16 = leBytes 8 (m.readW p 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64,
    VG.Proof.Poly1305.bytesAt_leBytes_64]

theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 656 16] s s' ∧
      bytesAt s'.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o0 := hp.in_ctx (a := 656) (w := 8) (by omega)
  have o1 := hp.in_ctx (a := 664) (w := 8) (by omega)
  rw [← h.wr] at o0 o1
  have core : WP isa (.block lengths) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (s.mem.writeW (off (cx s₀) 656) (s.gpr .x25)).writeW (off (cx s₀) 664) (s.gpr .x23) :=
    wp_str (a := off (cx s₀) 656) (by decide) (by rw [h.x21]) o0 fun s₁ g₁ =>
      wp_str (a := off (cx s₀) 664) (by decide) (by rw [g₁.gpr, h.x21]) (by rw [g₁.wr]; exact o1)
        fun s₂ g₂ => WP.block_nil ⟨by rw [g₂.rd, g₁.rd], by rw [g₂.wr, g₁.wr], by rw [g₂.mem, g₁.gpr, g₁.mem]⟩
  refine WP.mono (WP.kept core (by simp [lengths, dstOf, preserved])) fun s' ⟨⟨hrd, hwr, hm⟩, hg, hsp⟩ => ?_
  have hk : Kept [sub s₀ 656 16] s s' := Kept.of hg hsp hrd hwr (by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega)))
  refine ⟨h.step1 hk (by omega) (by omega) (by omega), hk, ?_⟩
  rw [bytesAt_16, off_off, show 656 + 8 = 664 from rfl, hm, readW64_off _ _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, h.x25, h.x23]

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem one32 : ((((1 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 1 := rfl

theorem cryptA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
      mov .x2 .x23, .addImm .x .x3 .x21 128]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = dp s₀ ∧ s'.gpr .x2 = s₀.gpr .x4 ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      Kept [sub s₀ 64 64] s s' := by
  have o := hp.in_ctx (a := 112) (w := 4) (by omega)
  rw [← h.wr] at o
  have core : WP isa (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
      mov .x2 .x23, .addImm .x .x3 .x21 128]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = dp s₀ ∧ s'.gpr .x2 = s₀.gpr .x4 ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      wp_addImm (by decide) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, one32]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x22]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x23]
    · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [mov, dstOf, preserved]))
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))

theorem hL (s₀ : State) : s₀.gpr .x4 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The data encrypted (or decrypted) from block counter 1. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 64 384, dR s₀] s s' ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, x0₁, x1₁, x2₁, x3₁, k₁⟩ => ?_)
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr₁, hp.wr], 64, rfl, by show 64 + 64 ≤ 1024; omega⟩
    · exact ⟨dR s₀, by simp [wr₁, hp.wr], 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by simp [wr₁, hp.wr], 128, rfl, by show 128 + 320 ≤ 1024; omega⟩
  refine xor_call x0₁ x1₁ (by rw [x2₁]; exact hL s₀) x3₁ (s₀.gpr .x4).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by omega) (by omega) (by omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by omega))) hp.wrap_d
    (covers_nil_append (covers_left _ hw)) hw fun s₂ k₂ data₂ => ?_
  have hsub : ∀ r ∈ [sub s₀ 64 384, dR s₀], ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by omega) (by omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  have hk : Kept [sub s₀ 64 384, dR s₀] s s₂ := by
    refine (k₁.sub fun r hr => ?_).trans (k₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by omega) (by omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
  refine ⟨h.step hk hsub (fun r hr => ?_), hk, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by omega))
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by omega))).symm) (s₀.gpr .x4).isLt.le
    have st₁ : stateAt s₁.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
        stateAt_writeW_counter, hst, set12_initState]
    rw [← bytesAt_eq, data₂, st₁, bytesAt_eq, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## Absorbing the lengths and the tag -/

/-- The lengths block absorbed. -/
theorem absorbLengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa absorbLengths s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 656) 16) := by
  unfold absorbLengths
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 656) (by omega) (by omega) 1 s)
    fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h1
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by omega)
    (sub_disj s₀ (b := 656) (m := 16 * 1) (by omega) (by omega) (by omega))
    (by rw [hp.off_toNat (by omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₁ (a := 448) (n := 128) (b := 656) (m := 16 * 1) (by omega) (by omega))
    (covers1 hp wr₁ (a := 448) (n := 128) (by omega)) fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ := (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by omega) (by omega) k₂)
  exact ⟨mac_inv h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- `x0 = x21 + 448`, `x1 = 0`, `x2 = x21 + out` and `x3 = x21 + 672`. -/
theorem fptrs_ok {out : Nat} (ho : out < 4096) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
      .addImm .x .x3 .x21 672]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = off (s.gpr .x21) out ∧
      Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
      .addImm .x .x3 .x21 672]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = off (s.gpr .x21) out ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm ho fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (640 ≤ out ∧ out + 16 ≤ 656)) :
    WP isa (finalizeTo out) s fun s' => Kept [sub s₀ 448 128, sub s₀ out 16] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (off (cx s₀) out) 16 = mac key msg := by
  unfold finalizeTo
  refine WP.seq (WP.mono (fptrs_ok (out := out) (by omega) s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have ho : out + 16 ≤ 1024 := by omega
  refine finalize_call h0 h1 h2 (sub_disj s₀ (by omega) (by omega) ho)
    (covers_left _ (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

/-! ## Restoring the registers -/

theorem restore_eq : restore =
    [.ldr .x .x22 .x21 600, .ldr .x .x23 .x21 608, .ldr .x .x24 .x21 616, .ldr .x .x25 .x21 624,
     .ldr .x .x30 .x21 632, .ldr .x .x21 .x21 592] := rfl

theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hsv : Saved s₀ s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      ((∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem) ∧ s'.sp = s.sp := by
  have i : ∀ d, d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hsv
  rw [restore_eq]
  refine WP.withSp ?_
  refine wp_ldr (a := off (cx s₀) 600) (by decide) (by rw [hx21]) (i 600 (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := off (cx s₀) 608) (by decide) (by rw [u₁.other _ (by decide), hx21])
    (by rw [u₁.rd, u₁.wr]; exact i 608 (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (a := off (cx s₀) 616) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 616 (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (a := off (cx s₀) 624) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 624 (by omega)) fun s₄ u₄ => ?_
  refine wp_ldr (a := off (cx s₀) 632) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 632 (by omega)) fun s₅ u₅ => ?_
  refine wp_ldr (a := off (cx s₀) 592) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 592 (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨fun r hr => ?_, fun r hr => ?_, by rw [u₆.mem, hm₅]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.gpr, hm₅, v1]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v2]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v3]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, v4]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, v5]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h21, h22, h23, h24, h25, h30⟩ := hr
    rw [u₆.other _ h21, u₅.other _ h30, u₄.other _ h25, u₃.other _ h24, u₂.other _ h23, u₁.other _ h22]

/-! ## Comparing the tags -/

theorem bytesAt_8_eq {m : Mem} {p q : Addr} :
    bytesAt m p 8 = bytesAt m q 8 ↔ m.readW p 64 = m.readW q 64 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Poly1305.leNum_bytesAt_64, ← VG.Proof.Poly1305.leNum_bytesAt_64, h]
  · intro h
    rw [VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (off p 8) 64 ^^^ m.readW (off q 8) 64)) = 0#64 ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, show 16 = 8 + 8 from rfl,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, ← bytesAt_8_eq, ← bytesAt_8_eq]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro h
    exact List.append_inj h (by rw [VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt])

/-- `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 64) : (x ||| (0 - x)) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 63 ≤ (x ||| (0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h2 | h2
      · exact Nat.le_trans (by omega) (Nat.right_le_or (n := x.toNat))
      · exact Nat.le_trans h2 Nat.left_le_or
    have h2 := (x ||| (0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

theorem sel_eq {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    ((1 : BitVec 64) - if x = 0 then 0 else 1).setWidth 32 = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide


theorem compare_ok
 {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block Impl.ChaCha20Poly1305.AArch64.compare) s fun s' =>
      (s'.gpr .x0).setWidth 32 =
        (if bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16 then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have core : WP isa (.block Impl.ChaCha20Poly1305.AArch64.compare) s fun s' =>
      s'.gpr .x0 = BitVec.ofNat 64 1 - ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
        (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64) |||
        (0 - ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
        (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64)))) >>> 63 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    unfold Impl.ChaCha20Poly1305.AArch64.compare
    refine wp_ldr (a := off (cx s₀) 640) (by decide) (by rw [hx21]) (i 640 (by omega)) fun s₁ u₁ => ?_
    refine wp_ldr (a := off (cx s₀) 48) (by decide) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.rd, u₁.wr]; exact i 48 (by omega)) fun s₂ u₂ => ?_
    refine wp_eor fun s₃ u₃ => ?_
    refine wp_ldr (a := off (cx s₀) 648) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 648 (by omega)) fun s₄ u₄ => ?_
    refine wp_ldr (a := off (cx s₀) 56) (by decide)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        hx21])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 56 (by omega)) fun s₅ u₅ => ?_
    refine wp_eor fun s₆ u₆ => wp_orr fun s₇ u₇ => wp_movz fun s₈ u₈ => wp_sub fun s₉ u₉ =>
      wp_orr fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_movz fun s₁₂ u₁₂ =>
      wp_sub fun s₁₃ u₁₃ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · have x9₃ : s₃.gpr .x9 = s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64 := by
        rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
      have x10₆ : s₆.gpr .x10 = s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      have x9₇ : s₇.gpr .x9 = (s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
          (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64) := by
        rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), x9₃, x10₆]
      rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₉.gpr,
        u₈.other _ (by decide), u₈.gpr, x9₇]
      rfl

    · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
        u₁.mem]
    · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [Impl.ChaCha20Poly1305.AArch64.compare, dstOf, preserved]))
    fun s' ⟨⟨h0, hm, hrd', hwr'⟩, hg, hsp⟩ => ⟨?_, hg, hsp, hm, hrd', hwr'⟩
  have ht := tag_eq s.mem (off (cx s₀) 640) (off (cx s₀) 48)
  simp only [off_off, Nat.reduceAdd] at ht
  rw [h0, nz_bit]
  exact sel_eq ht




end VG.Proof.ChaCha20Poly1305.AArch64
