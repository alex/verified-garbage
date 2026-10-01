import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_keygen`, the prologue and `G(d ‖ 3)`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- `d`, bytes `[0, 32)` of the seed. -/
abbrev dB (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0 + BitVec.ofNat 64 0) 32
/-- `z`, bytes `[32, 64)` of the seed. -/
abbrev zB (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0 + BitVec.ofNat 64 32) 32

theorem KB.d {s₀ s : State} (h : KB s₀ s) : bytesAt s.mem (kA s₀ 0 + BitVec.ofNat 64 0) 32 = dB s₀ := by
  rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), h.seed, bytesAt_take _ _ (by decide)]

theorem KB.z {s₀ s : State} (h : KB s₀ s) : bytesAt s.mem (kA s₀ 0 + BitVec.ofNat 64 32) 32 = zB s₀ := by
  have e : ∀ m : Mem, bytesAt m (kA s₀ 0 + BitVec.ofNat 64 32) 32 =
      (bytesAt m (kA s₀ 0 + BitVec.ofNat 64 0) 64).drop 32 := fun m => by
    rw [bytesAt_drop _ _ (by decide), ptr_add]
  rw [e, h.seed, ← e]

/-- Stores of the registers `rs` at `B + off + 8k`. -/
theorem saves_ok (B : Addr) (base : Reg) (off : Nat) (rs : List Reg) (hoff : off + 8 * rs.length ≤ 32768)
    (h8 : off % 8 = 0) :
    ∀ n ≤ rs.length, ∀ {s : State}, s.gpr base = B →
      (∀ k < rs.length, InRegions s.wr (B + BitVec.ofNat 64 (off + 8 * k)) 8) →
      WP isa (.block ((List.range n).map fun k => .str .x (rs.getD k .x0) base (off + 8 * k))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        (∀ k < n, s'.mem.readW (B + BitVec.ofNat 64 (off + 8 * k)) 64 = s.gpr (rs.getD k .x0)) ∧
        Frame [⟨B + BitVec.ofNat 64 off, 8 * rs.length⟩] s.mem s'.mem := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | succ n ih =>
    intro hn s hb hin
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) hb hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := B + BitVec.ofNat 64 (off + 8 * n)) (by constructor <;> omega) (by rw [g₁, hb])
      (by rw [w₁]; exact hin n (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [show B + BitVec.ofNat 64 (off + 8 * n) = B + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * n) by
        rw [ptr_add]]
      exact contains_off (by omega) (by omega)

theorem prologue_eq : kgPrologue =
    (List.range 6).map (fun k => .str .x (own.getD k .x0) .x3 (SV + 8 * k)) ++
      ([mov .x25 .x0, mov .x26 .x1, mov .x27 .x2, mov .x28 .x3, .movz .x .x24 1 0, .movz .x .x9 3 0,
        .strb .x9 .x28 B3] : List Instr) := rfl

/-- What the prologue leaves. -/
structure AfterPro (s₀ s : State) : Prop where
  kb : KB s₀ s
  x24 : s.gpr .x24 = 1
  b3 : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 B3) 1 = [BitVec.ofNat 8 3]

theorem pres_pro : ∀ r ∈ preserved, r ∉ own → r ∉ [Reg.x25, .x26, .x27, .x28, .x24, .x9] := by decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block kgPrologue) s₀ (AfterPro s₀) := by
  rw [prologue_eq, WP.block_append_iff]
  have hin : ∀ k < own.length, InRegions s₀.wr (kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk => by
    rw [hp.wr]
    exact in_regions (R := ⟨kA s₀ 3, kL 3⟩) (by simp) (contains_off (by simp at hk; simp only [SV, kL]; omega)
      (by decide))
  refine WP.mono (WP.preservedV (saves_ok (kA s₀ 3) .x3 SV own (by decide) (by decide) 6 (by decide) rfl hin) (hc := by decide +kernel))
    fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, vc₁⟩ => ?_
  refine wp_mov fun s₂ h₂ e₂ => wp_mov fun s₃ h₃ e₃ => wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => ?_
  have k₇ := (((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).keep
  have c28 : s₇.gpr .x28 = kA s₀ 3 := by
    rw [h₇.get .x28, h₆.get .x28, e₅, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]; rfl
  refine wp_strb (a := kA s₀ 3 + BitVec.ofNat 64 B3) (by decide) (by rw [c28])
    (by rw [k₇.wr, w₁, hp.wr]
        exact in_regions (R := ⟨kA s₀ 3, kL 3⟩) (by simp) (contains_off (by decide) (by decide)))
    fun s₈ h₈ => wp_nil ?_
  have m₈ : s₈.mem = s₁.mem.writeW (kA s₀ 3 + BitVec.ofNat 64 B3) ((s₇.gpr .x9).setWidth 8) := by
    rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem]
  have k₈ := k₇.trans h₈.keep
  have hf : Frame [R (kA s₀) 3 SV 48, R (kA s₀) 3 B3 1] s₀.mem s₈.mem := by
    rw [m₈]
    refine Frame.writeW (r := R (kA s₀) 3 B3 1) (Frame.mono f₁ fun r hr => ?_)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
  refine ⟨⟨by rw [k₈.rd, r₁], by rw [k₈.wr, w₁], by rw [k₈.sp, p₁], ?_, ?_, ?_, by rw [h₈.gpr]; exact c28,
    fun r hr ho => ?_, ?_, ?_, fun r hr => (k₈.vcs r hr).trans (vc₁ r hr)⟩, ?_, ?_⟩
  · rw [h₈.gpr, h₇.get .x25, h₆.get .x25, h₅.get .x25, h₄.get .x25, h₃.get .x25, e₂, g₁]; rfl
  · rw [h₈.gpr, h₇.get .x26, h₆.get .x26, h₅.get .x26, h₄.get .x26, e₃, h₂.get .x1, g₁]; rfl
  · rw [h₈.gpr, h₇.get .x27, h₆.get .x27, h₅.get .x27, e₄, h₃.get .x2, h₂.get .x2, g₁]; rfl
  · rw [k₈.gpr r (pres_pro r hr ho), g₁]
  · intro k hk
    rw [← z₁ k hk, m₈]
    exact Mem.readW_writeW_sep (sep_off _ (by simp only [SV, B3]; omega) (by simp only [SV]; omega)
      (by decide)) (by decide)
  · refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    rcases mem2' hr with rfl | rfl
    · exact R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [h₈.gpr, h₇.get .x24, e₆]; rfl
  · rw [m₈]
    refine bytesAt_eq (by rfl) fun i hi => ?_
    have : i = 0 := by omega
    subst this
    rw [ptr_zero, writeW8_apply, ite_eq_left rfl, e₇]
    rfl

/-! ## Hashes -/

/-- An output of a hash: bytes `[o, o + l)` of `ek`, `dk` or `scratch`, apart
from the saved registers. -/
def OutOk (p : Piece) : Prop :=
  ∃ b o l, p = ⟨breg b, o, l⟩ ∧ 1 ≤ b ∧ b < 4 ∧ o + l ≤ kL b ∧ (b ≠ 3 ∨ SV + 48 ≤ o ∨ o + l ≤ SV)

/-- A hash keeps what holds throughout. -/
theorem KB.hash {s₀ s s' : State} (hp : Pre s₀) (h : KB s₀ s) {outs : List Piece}
    (hk : Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: outs.map (preg s)) s s')
    (ho : ∀ p ∈ outs, OutOk p) : KB s₀ s' := by
  refine h.call hk fun r hr => ?_
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.STr, e]
    exact ⟨R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide),
      R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.WKr, e]
    exact ⟨R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide),
      R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h.sp]
    exact ⟨below_R hp (by decide) (by decide), below_R hp (by decide) (by decide)⟩
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  obtain ⟨b, o, l, rfl, h1, h4, f, hs⟩ := ho p hp'
  simp only [preg, h.breg h4]
  exact ⟨R.disj hp.args (by decide) h4 (by decide) f (by simp only [SV] at hs ⊢; omega),
    R.disj hp.args (by decide) h4 (by decide) f (by omega)⟩

theorem sha3Suffix_eq : Spec.Sha3.sha3Suffix = BitVec.ofNat 8 6 := rfl
theorem shakeSuffix_eq : Spec.Sha3.shakeSuffix = BitVec.ofNat 8 0x1f := rfl

/-- After `G(d ‖ 3)`. -/
structure AfterA (s₀ s : State) : Prop where
  kb : KB s₀ s
  x24 : s.gpr .x24 = 1
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = kgRho (dB s₀)
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = kgSigma (dB s₀)

theorem g_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : AfterPro s₀ s) : WP isa (kgGWith keccak.callee) s (AfterA s₀) := by
  have e : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by
    rw [h.kb.x28]
  refine WP.mono (hashWith_ok keccak (hsetup hp h.kb (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x25, 0, 32⟩, ⟨.x28, B3, 1⟩]) (outs := [⟨.x28, SB, 32⟩, ⟨.x28, SG, 32⟩]) (by simp)
    (fun p hp' => ?_) (fun p hp' => ?_) ?_) fun s' ⟨k', o'⟩ => ?_
  · rcases mem2' hp' with rfl | rfl
    · exact pieceOk (b := 0) hp h.kb (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pieceOk (b := 3) hp h.kb (by decide) (by decide) (by decide) (by decide) (by decide)
  · rcases mem2' hp' with rfl | rfl
    · exact pieceOk (b := 3) hp h.kb (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pieceOk (b := 3) hp h.kb (by decide) (by decide) (by decide) (by decide) (by decide)
  · refine List.pairwise_pair.mpr ?_
    simp only [preg, e]
    exact R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide)
  have kb' := h.kb.hash hp k' fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, SB, 32, rfl, by decide, by decide, by decide, by decide⟩
    · exact ⟨3, SG, 32, rfl, by decide, by decide, by decide, by decide⟩
  have msg : (List.map (pbytes s) [⟨.x25, 0, 32⟩, ⟨.x28, B3, 1⟩]).flatten =
      dB s₀ ++ [BitVec.ofNat 8 3] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      h.kb.x25, e]
    rw [show kA s₀ 0 = kA s₀ 0 from rfl, KB.d h.kb, h.b3]
  obtain ⟨o₁, o₂, -⟩ := o'
  rw [msg, e] at o₁ o₂
  have hG := G_eq (dB s₀ ++ [BitVec.ofNat 8 3])
  refine ⟨kb', by rw [k'.cs _ (by decide) (by decide), h.x24], ?_, ?_⟩
  · rw [o₁, kgRho, hG]; rfl
  · rw [o₂, kgSigma, hG]; rfl

end VG.Proof.MlKem.AArch64.KeyGen
