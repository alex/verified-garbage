import VerifiedGarbage.Proof.MlKem.Arm.Prf
import VerifiedGarbage.Impl.MlKem1024.Arm.Top
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on 32-bit ARM: the `PRF`s

`Proof/MlKem/Arm/Prf.lean` for ML-KEM-1024's layout of `scratch`:
`SamplePolyCBD₂(PRF₂(σ, N))` (and its NTT) into polynomial `4 + N`, for `N <
9` (`prfBody_ok`, `prfLoop_ok`).
-/

namespace VG.Proof.MlKem1024.Arm

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm

/-! ## Addresses -/

/-- Arithmetic on the offsets in `scratch`. -/
macro "offs4" : tactic => `(tactic| (
  simp only [oPoly, oPrf, oNtt4, oSeed, oSigma, oAcc4, oTmp4, oAhat4, oSample4, oK, oKbar, oMsg, oHek, oCt4,
    oWork, oSave, oExtra, oG, oCin4]; omega))

theorem enc_slot4 : ∀ k < 17, encodable (BitVec.ofNat 32 (oPoly k)) = true := by decide

/-! ## One `PRF` -/

/-- What one `PRF` changes. -/
abbrev prfW (N : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (4 + N), 1024), (0, oNtt4, 1024)]

theorem cbdArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly 4))) s fun s' => Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 oPrf ∧ s'.gpr .r1 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly 4) := by
  have e1 : encodable (BitVec.ofNat 32 oPrf) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 4)) = true := by decide
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem nttArgs_ok {s : State} {P : BitVec 32} {N : Nat} (h7 : s.gpr .r7 = P) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) :
    WP isa (.block (slotAt .r0 .r9 (oPoly 4) ++ [ptrTo .r1 .r7 oNtt4])) s fun s' => Only s s' ∧
      s'.gpr .r0 = P + BitVec.ofNat 32 N <<< 10 + BitVec.ofNat 32 (oPoly 4) ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 oNtt4 := by
  have e1 : encodable (BitVec.ofNat 32 oNtt4) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 (oPoly 4)) = true := by decide
  run_block [ptrTo, slotAt, e1, e2, h7, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

theorem enc_le9 : ∀ n, n ≤ 9 → encodable (BitVec.ofNat 32 n) = true := by decide

theorem prfBody_ok {L : Lay} {s : State} (hc : Ctx L s) (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 9) (h9 : s.gpr .r9 = BitVec.ofNat 32 N) {σ : List Byte} (hσ : bytesAt s.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (prfBody4 withNtt N₁) s fun s' => KeptX [.r9] (L.RL (prfW N)) s s' ∧
      s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
      PolyIs s'.mem (L.A 0 (oPoly (4 + N))) (prfOut withNtt σ N) := by
  have hL := hc.ok
  have eo : oPoly (4 + N) = oPoly 4 + 1024 * N := by unfold oPoly; omega
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
  refine WP.seq (WP.mono (hash_ok (idx := fun _ => 0) MlKem.rate136 (by decide) (by decide) (by decide) hc₁
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have hc₂ := hc₁.kept k₂
  have g9₂ : s₂.gpr .r9 = BitVec.ofNat 32 N := by rw [k₂.cs .r9 (by decide) (by decide), g9₁]
  have prfB : bytesAt s₂.mem (L.A 0 oPrf) 128 = prf 2 σ (BitVec.ofNat 8 N) := by
    have := o₂.1
    simp only [Lay.pb, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    rw [bσ] at this
    rw [this, VG.Proof.MlKem.prf_eq]; rfl
  refine WP.seq (WP.mono (cbdArgs_ok hc₂.r7 g9₂) fun s₃ ⟨o₃, g0, g1⟩ => ?_)
  rw [slot_eq _ (by offs4), ← eo] at g1
  have hc₃ := hc₂.only o₃
  refine WP.seq (cbd2L hL g0 g1 (hc.sep00 (by offs4) (by offs4) (by offs4))
    (mem_rd_wr hc₃.buf0) hc₃.buf0 fun s₄ k₄ p₄ => ?_)
  rw [o₃.mem, prfB] at p₄
  have hc₄ := hc₃.kept k₄
  have g9₄ : s₄.gpr .r9 = BitVec.ofNat 32 N := by
    rw [k₄.cs .r9 (by decide) (by decide), o₃.cs .r9 (by decide) (by decide), g9₂]
  have fin : ∀ s₅, KeptX [.r9] (L.RL [(0, oPoly (4 + N), 1024), (0, oNtt4, 1024)]) s₄ s₅ →
      s₅.gpr .r9 = BitVec.ofNat 32 N → PolyIs s₅.mem (L.A 0 (oPoly (4 + N))) (prfOut withNtt σ N) →
      WP isa (.block (count .r9 N₁)) s₅ fun s' => KeptX [.r9] (L.RL (prfW N)) s s' ∧
        s'.gpr .r9 = BitVec.ofNat 32 (N + 1) ∧ s'.z = decide (N + 1 = N₁) ∧
        PolyIs s'.mem (L.A 0 (oPoly (4 + N))) (prfOut withNtt σ N) := fun s₅ k₅ g9₅ p₅ =>
    WP.mono (count_ok (by omega) (by omega) (enc_le9 _ hN₁) g9₅) fun s' ⟨k', g', z'⟩ => ⟨by
      exact ((k₁.weaken (by simp)).monoL (W' := prfW N) (by simp)).trans (((k₂.x _).monoL (by simp)).trans
        ((o₃.x _ _).trans (((k₄.x _).monoL (by simp)).trans ((k₅.monoL (by simp)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))))),
      g', z', polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₅⟩
  cases withNtt
  · refine WP.seq (WP.block_nil ?_)
    exact fin s₄ ((Kept.refl _ _).x _) g9₄ p₄
  · refine WP.seq (WP.seq (WP.mono (nttArgs_ok hc₄.r7 g9₄) fun s₅ ⟨o₅, g0', g1'⟩ => ?_))
    rw [slot_eq _ (by offs4), ← eo] at g0'
    have hc₅ := hc₄.only o₅
    refine nttL hL g0' g1' (hc.sep00 (by offs4) (by offs4) (by offs4)) hc₅.buf0 hc₅.buf0 (by rw [o₅.mem]; exact p₄)
      fun s₆ k₆ p₆ => fin s₆ (((o₅.kept _).trans k₆).x _) ?_ p₆
    rw [k₆.cs .r9 (by decide) (by decide), o₅.cs .r9 (by decide) (by decide), g9₄]

/-! ## The loop -/

/-- What the loop changes: the regions of `prfW`, with all its polynomials. -/
abbrev prfLW (N₀ N₁ : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 8), (0, 952, 1), (0, 1024, 128), (0, oPoly (4 + N₀), 1024 * (N₁ - N₀)),
    (0, oNtt4, 1024)]

structure PrfInv (L : Lay) (withNtt : Bool) (σ : List Byte) (N₀ N₁ : Nat) (s₀ : State) (t : Nat) (s : State) :
    Prop where
  kx : KeptX [.r9] (L.RL (prfLW N₀ N₁)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 (N₀ + t)
  sig : bytesAt s.mem (L.A 0 oSigma) 32 = σ
  slots : ∀ N, N₀ ≤ N → N < N₀ + t → PolyIs s.mem (L.A 0 (oPoly (4 + N))) (prfOut withNtt σ N)

theorem prfW_sig : ∀ N < 9, (prfW N).all (sep0 oSigma 32) = true := by decide

theorem prfW_slot' : ∀ N < 9, ∀ N' < 9, (N' == N || (prfW N).all (sep0 (oPoly (4 + N')) 1024)) = true := by
  decide

theorem prfW_slot {N N' : Nat} (hN : N < 9) (hN' : N' < 9) (h : N' ≠ N) :
    (prfW N).all (sep0 (oPoly (4 + N')) 1024) = true := by
  have := prfW_slot' N hN N' hN'
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact this.resolve_left h

theorem prfStep_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (hN₁ : N₁ ≤ 9)
    {σ : List Byte} {t : Nat} (ht : t < N₁ - N₀) {s : State} (h : PrfInv L withNtt σ N₀ N₁ s₀ t s) :
    WP isa (prfBody4 withNtt N₁) s fun s' =>
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
    · exact ⟨L.R 0 (oPoly (4 + N₀)) (1024 * (N₁ - N₀)), by simp, hc.sub0 (by offs4) (by offs4) (by offs4)⟩
    · exact ⟨L.R 0 oNtt4 1024, by simp, fun _ h => h⟩
  · rw [← h.sig]
    exact Lay.bytes_keep hL k'.frame (hc.sepAll0 (by decide) (prfW_sig _ (by omega))) (by decide)
  · by_cases e : N = N₀ + t
    · subst e; exact p'
    · exact Lay.polyIs_keep hL k'.frame (hc.sepAll0 (by offs4) (prfW_slot (by omega) (by omega) e))
        (h.slots N h1 (by omega))
  · rw [z']; simp only [decide_eq_decide]; omega

theorem prfLoop_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 9) {σ : List Byte} (hσ : bytesAt s₀.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (prfLoop4 withNtt N₀ N₁) s₀ fun s => KeptX [.r9] (L.RL (prfLW N₀ N₁)) s₀ s ∧
      ∀ N, N₀ ≤ N → N < N₁ → PolyIs s.mem (L.A 0 (oPoly (4 + N))) (prfOut withNtt σ N) := by
  refine WP.seq (WP.mono (mov9_ok (enc_le9 _ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ => ?_)
  exact wp_loop_ne (PrfInv L withNtt σ N₀ N₁ s₀) (N := N₁ - N₀) (by omega)
    (fun t ht s h => prfStep_ok hc withNtt hN₁ ht h)
    (fun s h => ⟨h.kx, fun N h1 h2 => h.slots N h1 (by omega)⟩)
    ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ,
      fun N h1 h2 => absurd h2 (by omega)⟩

end VG.Proof.MlKem1024.Arm
