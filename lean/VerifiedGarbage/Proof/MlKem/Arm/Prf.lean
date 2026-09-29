import VerifiedGarbage.Proof.MlKem.Arm.Loops

/-!
# ML-KEM-768 on 32-bit ARM: sampling with `PRF` and `SamplePolyCBD`

Untrusted: everything here is checked by Lean. `prfLoop withNtt N₀ N₁`
writes `SamplePolyCBD₂(PRF₂(σ, N))` (its NTT if `withNtt`) to polynomial
`3 + N` for `N₀ ≤ N < N₁` (`prfLoop_ok`), with `σ` at offset 920 of
`scratch`, and changes only the regions of `prfW`.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom rates)

/-! ## What changes, but for some callee-saved registers -/

/-- `s'` differs from `s` only in memory within `rs`, in registers that are
not callee-saved (or are `lr`), and in the callee-saved registers `xs`. -/
structure KeptX (xs : List Reg) (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → r ∉ xs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.x {rs : List Region} {s s' : State} (h : Kept rs s s') (xs : List Reg) : KeptX xs rs s s' :=
  ⟨fun r hr hl _ => h.cs r hr hl, h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.trans {xs : List Reg} {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : KeptX xs rs s₁ s₂)
    (h₂ : KeptX xs rs s₂ s₃) : KeptX xs rs s₁ s₃ :=
  ⟨fun r hr h hx => by rw [h₂.cs r hr h hx, h₁.cs r hr h hx], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem KeptX.sub {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem KeptX.mono {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

theorem KeptX.weaken {xs ys : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hx : ∀ x ∈ xs, x ∈ ys) : KeptX ys rs s s' :=
  ⟨fun r hr hl hy => h.cs r hr hl fun hm => hy (hx r hm), h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.monoL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s s' : State}
    (h : KeptX xs (L.RL W) s s') (hs : ∀ w ∈ W, w ∈ W') : KeptX xs (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

theorem Only.x {s s' : State} (h : Only s s') (xs : List Reg) (rs : List Region) : KeptX xs rs s s' :=
  (h.kept rs).x xs

theorem KeptX.ctx {L : Lay} {xs : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (h7 : Reg.r7 ∉ xs) (hc : Ctx L s) : Ctx L s' :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide) h7, hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

/-- A region of `scratch` apart from the region `w` of `scratch` or of the stack. -/
def sep0 (o l : Nat) (w : Nat × Nat × Nat) : Bool :=
  (w.1 == 0 && decide (w.2.1 + w.2.2 ≤ 32768) && (decide (o + l ≤ w.2.1) || decide (w.2.1 + w.2.2 ≤ o))) ||
    (w.1 == 1 && decide (w.2.1 + w.2.2 ≤ 8))

theorem Ctx.sepAll0 {L : Lay} {s : State} (hc : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768)
    {W : List (Nat × Nat × Nat)} (h : W.all (sep0 o l) = true) : sepAll L.sizes (0, o, l) W = true := by
  refine List.all_eq_true.mpr fun w hw => ?_
  have h' := List.all_eq_true.mp h w hw
  obtain ⟨i, a, b⟩ := w
  simp only [sep0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  rcases h' with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
  · subst h1; exact hc.sep00 hl h2 h3
  · subst h1; exact hc.sep01 hl h2

/-- A part of `scratch` inside a bigger one. -/
theorem Ctx.sub0 {L : Lay} {s : State} (hc : Ctx L s) {a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l')
    (h₃ : b + l' ≤ 32768) : Region.Sub (L.R 0 a l) (L.R 0 b l') := by
  have := hc.fit
  have := addr_toNat (L.ptr 0)
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- `w` inside `w'`, a region of `scratch` or of the stack. -/
def subB0 (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2) &&
    ((w'.1 == 0 && decide (w'.2.1 + w'.2.2 ≤ 32768)) || (w'.1 == 1 && decide (w'.2.1 + w'.2.2 ≤ 8)))

theorem Lay.R_sub_R {L : Lay} (hL : L.Ok) {i a l b l' : Nat} (hi : i < L.sizes.length) (h₁ : b ≤ a)
    (h₂ : a + l ≤ b + l') (h₃ : b + l' ≤ L.size i) : Region.Sub (L.R i a l) (L.R i b l') := by
  have hf : (L.ptr i).toNat + L.size i ≤ 2 ^ 32 := hL.fit i hi
  have := addr_toNat (L.ptr i)
  have := h₃
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem Ctx.subL {L : Lay} {s : State} (hc : Ctx L s) {W W' : List (Nat × Nat × Nat)}
    (h : W.all (fun w => W'.any (subB0 w)) = true) : ∀ r ∈ L.RL W, ∃ r' ∈ L.RL W', Region.Sub r r' := by
  intro r hr
  obtain ⟨⟨i, a, l⟩, hw, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨i', b, l'⟩, hw', hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h _ hw)
  simp only [subB0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨e, h₁⟩, h₂⟩, h₃⟩ := hs
  subst e
  refine ⟨L.R i b l', List.mem_map.mpr ⟨_, hw', rfl⟩, Lay.R_sub_R hc.ok ?_ h₁ h₂ ?_⟩
  · have := hc.len; rcases h₃ with ⟨e, -⟩ | ⟨e, -⟩ <;> subst e <;> omega
  · rcases h₃ with ⟨e, h⟩ | ⟨e, h⟩ <;> subst e
    · rw [hc.sz0]; exact h
    · rw [hc.sz1]; exact h

theorem KeptX.subL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s₀ s s' : State} (hc : Ctx L s₀)
    (h : KeptX xs (L.RL W) s s') (hb : W.all (fun w => W'.any (subB0 w)) = true) : KeptX xs (L.RL W') s s' :=
  h.sub (hc.subL hb)

/-! ## Addresses -/

/-- Arithmetic on the offsets in `scratch`. -/
macro "offs" : tactic => `(tactic| (
  simp only [oPoly, oPrf, oNtt, oSeed, oSigma, oAcc, oTmp, oAhat, oSample, oK, oKbar, oMsg, oHek, oCt, oWork,
    oSave, oExtra, oG]; omega))

theorem slot_eq (p : BitVec 32) {N off : Nat} (_h : off + 1024 * N < 2 ^ 32) :
    p + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 off = p + BitVec.ofNat 32 (off + 1024 * N) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem enc_slot : ∀ k < 14, encodable (BitVec.ofNat 32 (oPoly k)) = true := by decide

theorem setWidth8_ofNat {N : Nat} (h : N < 2 ^ 32) : (BitVec.ofNat 32 N).setWidth 8 = BitVec.ofNat 8 N := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Counters -/

theorem count_ok {s : State} {c : Reg} {n k : Nat} (hk : k + 1 < 2 ^ 32)
    (hn : n < 2 ^ 32) (hen : encodable (BitVec.ofNat 32 n) = true) (h : s.gpr c = BitVec.ofNat 32 k) :
    WP isa (.block (count c n)) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 32 (k + 1) ∧ s'.z = decide (k + 1 = n) := by
  have e1 : encodable (BitVec.ofNat 32 1) = true := by decide
  run_block [count, hen, e1, h]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, by rw [BitVec.ofNat_add]; rfl, ?_⟩
  · show (if r = c then _ else s.gpr r) = s.gpr r
    exact ite_eq_right (fun e : r = c => hx (by rw [e]; exact List.mem_singleton_self _))
  · rw [show BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) by rw [BitVec.ofNat_add]; rfl, cmp_z _ _ hn,
      toNat_ofNat32 hk]

/-! ## One `PRF` -/

/-- Polynomial `3 + N`: `SamplePolyCBD₂(PRF₂(σ, N))`, or its NTT. -/
def prfOut (withNtt : Bool) (σ : List Byte) (N : Nat) : Poly :=
  if withNtt then ntt (VG.Proof.MlKem.cbd σ N) else VG.Proof.MlKem.cbd σ N

/-- What one `PRF` changes. -/
abbrev prfW (N : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (3 + N), 1024), (0, oNtt, 1024)]

theorem bytes_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem strb9_ok {L : Lay} {s : State} (hc : Ctx L s) {N : Nat} (hN : N < 2 ^ 32)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block [.strb .r9 .r7 (oSigma + 32)]) s fun s₁ =>
      KeptX [] (L.RL [(0, 952, 1)]) s s₁ ∧ s₁.mem = s.mem.writeW (L.A 0 952) (BitVec.ofNat 8 N) := by
  have e952 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oSigma + 32)) = L.A 0 952 := by
    rw [hc.r7]; exact hc.addr (by decide)
  have i952 : InRegions s.wr (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oSigma + 32))) 1 := by
    rw [e952]; exact hc.cs (o := 952) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have ho : oSigma + 32 < 4096 := by decide
  run_block [i952, ho]
  refine ⟨⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · show Frame _ s.mem (s.mem.writeW _ _)
    rw [e952]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · show s.mem.writeW _ _ = _
    rw [e952, h9, setWidth8_ofNat hN]

theorem cbdArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly 3))) s fun s' => Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 oPrf ∧ s'.gpr .r1 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly 3) := by
  have e1 : encodable (BitVec.ofNat 32 oPrf) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem nttArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (slotAt .r0 .r9 (oPoly 3) ++ [ptrTo .r1 .r7 oNtt])) s fun s' => Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly 3) ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 oNtt := by
  have e1 : encodable (BitVec.ofNat 32 oNtt) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem rate136 : 136 ∈ rates := by decide

theorem enc_le7 : ∀ n, n ≤ 7 → encodable (BitVec.ofNat 32 n) = true := by decide

theorem prfBody_ok {L : Lay} {s : State} (hc : Ctx L s) (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 7) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) {σ : List Byte} (hσ : bytesAt s.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (prfBody withNtt N₁) s fun s' => KeptX [.r9] (L.RL (prfW N)) s s' ∧
      s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
      PolyIs s'.mem (L.A 0 (oPoly (3 + N))) (prfOut withNtt σ N) := by
  have hL := hc.ok
  have eo : oPoly (3 + N) = oPoly 3 + 1024 * N := by unfold oPoly; omega
  refine WP.seq (WP.mono (strb9_ok hc (by omega) h9) fun s₁ ⟨k₁, m₁⟩ => ?_)
  have hc₁ := k₁.ctx (by decide) hc
  have g9₁ : s₁.gpr .r9 = BitVec.ofNat 32 N := by rw [k₁.cs .r9 (by decide) (by decide) (by decide), h9]
  have bσ : bytesAt s₁.mem (L.A 0 920) 33 = σ ++ [BitVec.ofNat 8 N] := by
    show bytesAt s₁.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 920) (32 + 1) = _
    rw [bytesAt_add, bytes_one, add_ofNat_add]
    congr 1
    · rw [← hσ]
      exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
    · rw [m₁, writeW8_apply, ite_eq_left rfl]
  have hin : ∀ p ∈ [(⟨.r7, oSigma, 33⟩ : Piece)], PieceOk L (fun _ => 0) s₁ false p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨⟨by decide, by decide⟩, hc₁.r7, by decide, by decide, by decide, by decide,
      hc₁.sepAll0 (by decide) (by decide), mem_rd_wr hc₁.buf0⟩
  have hout : ∀ p ∈ [(⟨.r7, oPrf, 128⟩ : Piece)], PieceOk L (fun _ => 0) s₁ true p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨⟨by decide, by decide⟩, hc₁.r7, by decide, by decide, by decide, by decide,
      hc₁.sepAll0 (by decide) (by decide), hc₁.buf0⟩
  refine WP.seq (WP.mono (hash_ok (idx := fun _ => 0) rate136 (by decide) (by decide) (by decide) hc₁
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have hc₂ := hc₁.kept k₂
  have g9₂ : s₂.gpr .r9 = BitVec.ofNat 32 N := by rw [k₂.cs .r9 (by decide) (by decide), g9₁]
  have prfB : bytesAt s₂.mem (L.A 0 oPrf) 128 = prf 2 σ (BitVec.ofNat 8 N) := by
    have := o₂.1
    simp only [Lay.pb, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    rw [bσ] at this
    rw [this, VG.Proof.MlKem.prf_eq]; rfl
  refine WP.seq (WP.mono (cbdArgs_ok hc₂.r7 g9₂) fun s₃ ⟨o₃, g0, g1⟩ => ?_)
  rw [slot_eq _ (by offs), ← eo] at g1
  have hc₃ := hc₂.only o₃
  refine WP.seq (cbd2L hL g0 g1 (hc.sep00 (by offs) (by offs) (by offs))
    (mem_rd_wr hc₃.buf0) hc₃.buf0 fun s₄ k₄ p₄ => ?_)
  rw [o₃.mem, prfB] at p₄
  have hc₄ := hc₃.kept k₄
  have g9₄ : s₄.gpr .r9 = BitVec.ofNat 32 N := by
    rw [k₄.cs .r9 (by decide) (by decide), o₃.cs .r9 (by decide) (by decide), g9₂]
  have fin : ∀ s₅, KeptX [.r9] (L.RL [(0, oPoly (3 + N), 1024), (0, oNtt, 1024)]) s₄ s₅ →
      s₅.gpr .r9 = BitVec.ofNat 32 N → PolyIs s₅.mem (L.A 0 (oPoly (3 + N))) (prfOut withNtt σ N) →
      WP isa (.block (count .r9 N₁)) s₅ fun s' => KeptX [.r9] (L.RL (prfW N)) s s' ∧
        s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
        PolyIs s'.mem (L.A 0 (oPoly (3 + N))) (prfOut withNtt σ N) := fun s₅ k₅ g9₅ p₅ =>
    WP.mono (count_ok (by omega) (by omega) (enc_le7 _ hN₁) g9₅) fun s' ⟨k', g', z'⟩ => ⟨by
      exact ((k₁.weaken (by simp)).monoL (W' := prfW N) (by simp)).trans (((k₂.x _).monoL (by simp)).trans
        ((o₃.x _ _).trans (((k₄.x _).monoL (by simp)).trans ((k₅.monoL (by simp)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))))),
      g', z', polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₅⟩
  cases withNtt
  · refine WP.seq (WP.block_nil ?_)
    exact fin s₄ ((Kept.refl _ _).x _) g9₄ p₄
  · refine WP.seq (WP.seq (WP.mono (nttArgs_ok hc₄.r7 g9₄) fun s₅ ⟨o₅, g0', g1'⟩ => ?_))
    rw [slot_eq _ (by offs), ← eo] at g0'
    have hc₅ := hc₄.only o₅
    refine nttL hL g0' g1' (hc.sep00 (by offs) (by offs) (by offs)) hc₅.buf0 hc₅.buf0 (by rw [o₅.mem]; exact p₄)
      fun s₆ k₆ p₆ => fin s₆ (((o₅.kept _).trans k₆).x _) ?_ p₆
    rw [k₆.cs .r9 (by decide) (by decide), o₅.cs .r9 (by decide) (by decide), g9₄]

/-! ## The loop -/

/-- What the loop changes: the regions of `prfW`, with all its polynomials. -/
abbrev prfLW (N₀ N₁ : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (3 + N₀), 1024 * (N₁ - N₀)),
    (0, oNtt, 1024)]

structure PrfInv (L : Lay) (withNtt : Bool) (σ : List Byte) (N₀ N₁ : Nat) (s₀ : State) (t : Nat) (s : State) :
    Prop where
  kx : KeptX [.r9] (L.RL (prfLW N₀ N₁)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 (N₀ + t)
  sig : bytesAt s.mem (L.A 0 oSigma) 32 = σ
  slots : ∀ N, N₀ ≤ N → N < N₀ + t → PolyIs s.mem (L.A 0 (oPoly (3 + N))) (prfOut withNtt σ N)

theorem prfW_sig : ∀ N < 7, (prfW N).all (sep0 oSigma 32) = true := by decide

theorem prfW_slot' : ∀ N < 7, ∀ N' < 7, (N' == N || (prfW N).all (sep0 (oPoly (3 + N')) 1024)) = true := by
  decide

theorem prfW_slot {N N' : Nat} (hN : N < 7) (hN' : N' < 7) (h : N' ≠ N) :
    (prfW N).all (sep0 (oPoly (3 + N')) 1024) = true := by
  have := prfW_slot' N hN N' hN'
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact this.resolve_left h

theorem mov9_ok {s : State} {N : Nat} (he : encodable (BitVec.ofNat 32 N) = true) :
    WP isa (.block [.mov .r9 (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      KeptX [.r9] [] s s' ∧ s'.gpr .r9 = BitVec.ofNat 32 N ∧ s'.mem = s.mem := by
  run_block [he]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r9 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r9 => hx (by rw [e]; exact List.mem_singleton_self _))

theorem prfStep_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (hN₁ : N₁ ≤ 7)
    {σ : List Byte} {t : Nat} (ht : t < N₁ - N₀) {s : State} (h : PrfInv L withNtt σ N₀ N₁ s₀ t s) :
    WP isa (prfBody withNtt N₁) s fun s' =>
      PrfInv L withNtt σ N₀ N₁ s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = N₁ - N₀) := by
  have hL := hc.ok
  have hcs := h.kx.ctx (by decide) hc
  refine WP.mono (prfBody_ok hcs withNtt (N := N₀ + t) (by omega) hN₁ h.r9 h.sig) fun s' ⟨k', g', z', p'⟩ =>
    ⟨⟨h.kx.trans (k'.sub fun r hr => ?_), by rw [g', Nat.add_assoc], ?_, fun N h1 h2 => ?_⟩, ?_⟩
  · simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.R 0 0 200, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 200 640, by simp, fun _ h => h⟩
    · exact ⟨L.R 1 0 8, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 952 1, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 1024 128, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 (oPoly (3 + N₀)) (1024 * (N₁ - N₀)), by simp, hc.sub0 (by offs) (by offs) (by offs)⟩
    · exact ⟨L.R 0 oNtt 1024, by simp, fun _ h => h⟩
  · rw [← h.sig]
    exact Lay.bytes_keep hL k'.frame (hc.sepAll0 (by decide) (prfW_sig _ (by omega))) (by decide)
  · by_cases e : N = N₀ + t
    · subst e; exact p'
    · exact Lay.polyIs_keep hL k'.frame (hc.sepAll0 (by offs) (prfW_slot (by omega) (by omega) e))
        (h.slots N h1 (by omega))
  · rw [z']; simp only [decide_eq_decide]; omega

theorem prfLoop_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 7) {σ : List Byte} (hσ : bytesAt s₀.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (prfLoop withNtt N₀ N₁) s₀ fun s => KeptX [.r9] (L.RL (prfLW N₀ N₁)) s₀ s ∧
      ∀ N, N₀ ≤ N → N < N₁ → PolyIs s.mem (L.A 0 (oPoly (3 + N))) (prfOut withNtt σ N) := by
  refine WP.seq (WP.mono (mov9_ok (enc_le7 _ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ => ?_)
  exact wp_loop_ne (PrfInv L withNtt σ N₀ N₁ s₀) (N := N₁ - N₀) (by omega)
    (fun t ht s h => prfStep_ok hc withNtt hN₁ ht h)
    (fun s h => ⟨h.kx, fun N h1 h2 => h.slots N h1 (by omega)⟩)
    ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ,
      fun N h1 h2 => absurd h2 (by omega)⟩

end VG.Proof.MlKem.Arm
