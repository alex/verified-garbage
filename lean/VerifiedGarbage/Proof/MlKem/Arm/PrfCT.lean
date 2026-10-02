import VerifiedGarbage.Proof.MlKem.Arm.CallsCT

/-!
# ML-KEM on 32-bit ARM: the `PRF`s in constant time

Two runs of `prfLoop` with the same `scratch` leak the same trace
(`prfLoop_ct`): every address is `scratch` plus an offset that depends only on
the counter `N`, and the calls take the same pointers in both runs. What each
run is at each point comes from its correctness (`relct_wp`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

theorem prf_hashOk {L : Lay} {s : State} (hc : Ctx L s) :
    HashOk L (fun _ => 0) [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩] s := by
  refine ⟨hc, fun p hp => ?_, fun p hp => ?_⟩ <;> rw [List.mem_singleton] at hp <;> subst hp
  · exact ⟨⟨by decide, by decide⟩, hc.r7, by decide, by decide, by decide, by decide,
      hc.sepAll0 (by decide) (by decide), mem_rd_wr hc.buf0⟩
  · exact ⟨⟨by decide, by decide⟩, hc.r7, by decide, by decide, by decide, by decide,
      hc.sepAll0 (by decide) (by decide), hc.buf0⟩

/-- A state `prfBody` runs from, as far as its timing is concerned. -/
abbrev PS (L : Lay) (N : Nat) (s : State) : Prop := Ctx L s ∧ s.gpr .r9 = BitVec.ofNat 32 N

theorem prfBody_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) :
    RelCT isa (fun a b => PS L N a ∧ PS L N b) (K.prfBody withNtt N₁) fun _ _ => True := by
  have k4 := hK.k4
  -- the counter
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (taint_block [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r7, hab.2.1.r7]) (by taint_decide))
      fun a b hab => ⟨WP.mono (strb9_ok hab.1.1 (by omega) hab.1.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.1.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.1.2]⟩,
        WP.mono (strb9_ok hab.2.1 (by omega) hab.2.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.2.1, by rw [k'.cs .r9 (by decide) (by decide) (by decide), hab.2.2]⟩⟩) ?_
  -- `PRF`
  have hh : ∀ s, PS L N s → WP isa (hash 136 0x1f [⟨.r7, oSigma, 33⟩] [⟨.r7, oPrf, 128⟩]) s (PS L N) :=
    fun s h => WP.mono (hash_ok rate136 (by decide) (by decide) (by decide) h.1 (List.cons_ne_nil _ _)
      (prf_hashOk h.1).ins (prf_hashOk h.1).outs (List.pairwise_singleton _ _)) fun s' ⟨k', _⟩ =>
      ⟨h.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (hash_ct rate136 (by decide) (by decide) (List.cons_ne_nil _ _) fun a b hab =>
      ⟨prf_hashOk hab.1.1, prf_hashOk hab.2.1, hab.1.1.sp_eq hab.2.1⟩) fun a b hab => ⟨hh a hab.1, hh b hab.2⟩) ?_
  -- `SamplePolyCBD₂`
  let F : State → Prop := fun s => PS L N s ∧ s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oPrf ∧
    s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + N))
  have eo : oPoly (K.k + N) = oPoly K.k + 1024 * N := by simp only [oPoly]; omega
  have ha : ∀ s, PS L N s → WP isa (.block (ptrTo .r0 .r7 oPrf :: slotAt .r1 .r9 (oPoly K.k))) s F :=
    fun s h => WP.mono (cbdArgs_ok hK h.1.r7 h.2) fun s' ⟨o', g0, g1⟩ =>
      ⟨⟨h.1.only o', by rw [o'.cs .r9 (by decide) (by decide), h.2]⟩, g0,
        by rw [g1, slot_eq _ (by offs), ← eo]⟩
  refine RelCT.seq (R := fun a b => F a ∧ F b) (relct_wp (relct_noMem rfl) fun a b hab => ⟨ha a hab.1, ha b hab.2⟩) ?_
  have hcb : ∀ s, F s → WP isa callCbd2 s (PS L N) := fun s h =>
    cbd2L h.1.1.ok h.2.1 h.2.2 (h.1.1.sep00 (by offs) (by offs) (by offs)) (mem_rd_wr h.1.1.buf0) h.1.1.buf0
      fun s' k' _ => ⟨h.1.1.kept k', by rw [k'.cs .r9 (by decide) (by decide), h.1.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (RelCT.callT cbd2T (regs2 fun a b hab => ⟨by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b hab => ⟨hcb a hab.1, hcb b hab.2⟩) ?_
  -- the NTT, and the counter
  cases withNtt
  · exact RelCT.seq (R := fun _ _ => True) (relct_noMem rfl) (relct_noMem rfl)
  · refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem rfl)
    let G : State → Prop := fun s => s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + N)) ∧
      s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt
    have hn : ∀ s, PS L N s → WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ [ptrTo .r1 .r7 K.oNtt])) s G :=
      fun s h => WP.mono (nttArgs_ok hK h.1.r7 h.2) fun s' ⟨_, g0, g1⟩ => ⟨by rw [g0, slot_eq _ (by offs), ← eo], g1⟩
    exact RelCT.seq (R := fun a b => G a ∧ G b) (relct_wp (relct_noMem rfl) fun a b hab => ⟨hn a hab.1, hn b hab.2⟩)
      (RelCT.callT nttT (regs2 fun a b hab => ⟨by rw [hab.1.1, hab.2.1], by rw [hab.1.2, hab.2.2]⟩))

theorem prfLoop_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1)
    {s₀₁ s₀₂ : State} (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂) {σ₁ σ₂ : List Byte}
    (hσ₁ : bytesAt s₀₁.mem (L.A 0 oSigma) 32 = σ₁) (hσ₂ : bytesAt s₀₂.mem (L.A 0 oSigma) 32 = σ₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.prfLoop withNtt N₀ N₁) fun _ _ => True := by
  have k4 := hK.k4
  refine RelCT.seq (R := fun a b => PrfInv K L withNtt σ₁ N₀ N₁ s₀₁ 0 a ∧ PrfInv K L withNtt σ₂ N₀ N₁ s₀₂ 0 b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨?_, ?_⟩) (RelCT.mono (relct_loop_ne (I₁ := PrfInv K L withNtt σ₁ N₀ N₁ s₀₁) (I₂ := PrfInv K L withNtt σ₂ N₀ N₁ s₀₂)
      (N := N₁ - N₀) (by omega) fun t ht => ?_)
      (fun _ _ h => h) fun _ _ _ => trivial)
  · rw [hab.1]
    exact WP.mono (mov9_ok (enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₁,
        fun N h1 h2 => absurd h2 (by omega)⟩
  · rw [hab.2]
    exact WP.mono (mov9_ok (enc_le9 N₀ (by omega))) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₂,
        fun N h1 h2 => absurd h2 (by omega)⟩
  -- one iteration: the body's timing from where it runs, and each run by correctness
  exact relct_wp (RelCT.mono (prfBody_ct hK (N := N₀ + t) withNtt (by omega) hN₁) (fun a b hab =>
      ⟨⟨hab.1.kx.ctx (by decide) hc₁, hab.1.r9⟩, ⟨hab.2.kx.ctx (by decide) hc₂, hab.2.r9⟩⟩) fun _ _ h => h)
    fun a b hab => ⟨prfStep_ok hK hc₁ withNtt hN₁ ht hab.1, prfStep_ok hK hc₂ withNtt hN₁ ht hab.2⟩

end VG.Proof.MlKem.Arm
