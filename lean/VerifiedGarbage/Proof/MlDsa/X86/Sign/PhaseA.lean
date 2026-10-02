import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local

/-!
# ML-DSA signing on x86 (32-bit): `ExpandA`

`ρ` is copied to `RS`, and entry `e` of `Â` (row `e / ℓ`, column `e % ℓ`) is
sampled into slot `aBase + e` from the seed `ρ ‖ e % ℓ ‖ e / ℓ` (`seedE`),
with `OK` the AND of the results (`okE`). After entry `e` (`IA e`): if every
entry so far succeeded, their slots hold them, within `maxBounds` (`aVal`);
otherwise one of them fails within `minBounds`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `ρ`, from the initial state. -/
abbrev rhoS (s₀ : State) : List Byte := rhoV (skOf p s₀)

/-- The seed of entry `e`. -/
abbrev seedE (s₀ : State) (e : Nat) : List Byte := aSeed (rhoS p s₀) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e`, within `maxBounds`. -/
abbrev aVal (s₀ : State) (e : Nat) : Poly := Av (skOf p s₀) (e / p.ℓ) (e % p.ℓ)

/-- The first `e` entries were sampled. -/
def okE (F : List Byte → Bool) (s₀ : State) (e : Nat) : Bool := (List.range e).all fun e' => F (seedE p s₀ e')

end

theorem okE_succ {F : List Byte → Bool} {s₀ : State} {e : Nat} :
    okE p F s₀ (e + 1) = (okE p F s₀ e && F (seedE p s₀ e)) := by
  simp only [okE, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem okE_lt {F : List Byte → Bool} {s₀ : State} {e e' : Nat} (h : okE p F s₀ e = true) (he : e' < e) :
    F (seedE p s₀ e') = true :=
  List.all_eq_true.mp h e' (List.mem_range.mpr he)

/-- After entry `e`. -/
structure IA (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  rs : bytesAt s.mem (Buf.addr s₀ (sc oRS 32)) 32 = rhoS p s₀
  ok : scw s₀ s oOK = if okE p F s₀ e then 1 else 0
  fam : okE p F s₀ e = true → Fam s₀ s.mem (aBase p) e (aVal p s₀)
  bad : okE p F s₀ e = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p s₀ e') = none

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem skLen_ge (ps : PS p) : 32 ≤ p.skLen := by have := ps.hskLen; omega

theorem rhoS_eq {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : rhoS p s₀ = rhoS p s₀' :=
  rho_of_leak (by rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps)
    (by rw [VG.Proof.MlKem.bytesAt_length]; exact skLen_ge ps) hq.2

/-! ## An entry -/

/-- The bytes of the layout an entry needs. -/
theorem okRS (ps : PS p) : (Y p).ok (sc oRS 32) = true ∧ (Y p).okW (sc (oRS + 32) 1) = true ∧
    (Y p).okW (sc (oRS + 33) 1) = true ∧ (Y p).ok (sc oRS 33) = true ∧ (Y p).ok (sc oRS 34) = true ∧
    (Y p).ok (sc (oRS + 32) 1) = true ∧ (Y p).ok (sc (oRS + 33) 1) = true :=
  ⟨sc_ok' ps (by decide) (by decide), sc_ok ps (by decide) (by decide), sc_ok ps (by decide) (by decide),
    sc_ok' ps (by decide) (by decide), sc_ok' ps (by decide) (by decide), sc_ok' ps (by decide) (by decide),
    sc_ok' ps (by decide) (by decide)⟩

theorem seed_bytes (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) {m : Mem} {ρ : List Byte} {i j : Nat}
    (hρ : bytesAt m (Buf.addr s₀ (sc oRS 32)) 32 = ρ)
    (hj : bytesAt m (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (Buf.addr s₀ (sc (oRS + 33) 1)) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m (Buf.addr s₀ (sc oRS 34)) 34 = aSeed ρ i j := by
  obtain ⟨o1, -, -, o4, o5, o6, o7⟩ := okRS ps
  rw [addr_off hp (d := 32) o5 o6] at hj
  rw [addr_off hp (d := 33) o5 o7] at hi
  rw [show Buf.addr s₀ (sc oRS 32) = Buf.addr s₀ (sc oRS 34) from rfl] at hρ
  rw [VG.Proof.MlKem.bytesAt_add _ _ 33 1, VG.Proof.MlKem.bytesAt_add _ _ 32 1, hρ, hj, hi, aSeed,
    integerToBytes_one, integerToBytes_one]

theorem rs_hi (ps : PS p) : oRS + 34 ≤ scrLen p := by
  have := scr_ge ps; simp only [oP, oRS, nS] at this ⊢; omega

/-- The two bytes of the seed of entry `e`. -/
theorem seedBlk_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (IA p F.rejF e) (fun s₀ s => IA p F.rejF e s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = seedE p s₀ e)
      (.block (st8 (oRS + 32) (e % p.ℓ) ++ st8 (oRS + 33) (e / p.ℓ))) := by
  obtain ⟨o1, w2, w3, -, -, -, -⟩ := okRS ps
  refine blk_piece (fun _ _ _ h => h.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st8 hp h.ctx w2 _ fun s₁ c₁ f₁ b₁ => ?_
  rw [← List.append_nil (st8 (oRS + 33) (e / p.ℓ))]
  refine wp_st8 hp c₁ w3 _ fun s₂ c₂ f₂ b₂ => WP.block_nil_iff.mpr ?_
  have fs : ∀ o, o = oRS + 32 ∨ o = oRS + 33 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oRS + 32 ≤ c.off ∧ c.off + c.len ≤ oRS + 34 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oRS, true_and] at ho ⊢; omega
  have f := (frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (rs_hi ps) (fs _ (.inl rfl)) f₁).trans
    (frSc hp (M := 0) (Nat.le_refl _) (by decide) (by decide) (rs_hi ps) (fs _ (.inr rfl)) f₂)
  have o0 : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p oOK (oOK + 4) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  have o1' : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p oRS (oRS + 32) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => by decide⟩
  have oF : ∀ c ∈ [sc (oRS + 32) (oRS + 34 - (oRS + 32))], Out p (oP (aBase p)) (oP (aBase p + e)) c := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc
    exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inl (by simp only [oP, oRS]; omega)⟩
  have hrs : bytesAt s₂.mem (Buf.addr s₀ (sc oRS 32)) 32 = rhoS p s₀ := by rw [keepB hp (by decide) f o1 o1', h.rs]
  refine ⟨⟨c₂, hrs, by rw [scw, keepW' hp (by decide) f (sc_ok' ps (by decide) (by decide)) o0]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) f (by simp only [nS, aBase]; omega) oF, h.bad⟩, ?_⟩
  have b₁' : bytesAt s₂.mem (Buf.addr s₀ (sc (oRS + 32) 1)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := by
    rw [keepB hp (by decide) f₂ (sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b₁]
  exact seed_bytes ps hp hrs b₁' b₂

/-- After the call of entry `e`. -/
structure RB (p : Params) (F : List Byte → Bool) (e : Nat) (s₀ s : State) : Prop where
  ia : IA p F e s₀ s
  eax : s.gpr .eax = if F (seedE p s₀ e) then 1 else 0
  yes : F (seedE p s₀ e) = true → PolyIs s.mem (Buf.addr s₀ (pS (aBase p + e))) (aVal p s₀ e)
  no : F (seedE p s₀ e) = false → rejNTTPoly minBounds.rejNTT (seedE p s₀ e) = none

theorem rej_lay (ps : PS p) {e : Nat} (he : e < p.k * p.ℓ) :
    ((Y p).ok ⟨SC, oRS, 34⟩ && (Y p).okW ⟨SC, oP (aBase p + e), 1024⟩ && (Y p).okW ⟨SC, oPS, 2048⟩ &&
      (Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, oP (aBase p + e), 1024⟩ && (Y p).sep ⟨SC, oRS, 34⟩ ⟨SC, oPS, 2048⟩ &&
      (Y p).sep ⟨SC, oP (aBase p + e), 1024⟩ ⟨SC, oPS, 2048⟩) = true := by ofs

/-- The call of entry `e`. -/
theorem rejCall_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (fun s₀ s => IA p F.rejF e s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (sc oRS 34)) 34 = seedE p s₀ e)
      (RB p F.rejF e)
      (callPR "vg_mldsa_rej_ntt_poly" P.rejNTT [.buf (sc oRS 34), .buf (pS (aBase p + e)), .buf bPS]) := by
  refine rej_piece F.rejNTT (F.ok _ (by simp)) SC oRS SC (oP (aBase p + e)) SC oPS (rej_lay ps he)
    (fun _ _ _ h => h.1.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => by
      rw [h.2, h'.2]; show aSeed (rhoS p s₀) _ _ = aSeed (rhoS p s₀') _ _; rw [rhoS_eq ps hq])
    fun s₀ s s' hp ⟨h, hs⟩ c' fr heax hred hout => ?_
  rw [hs] at heax hout
  have hj : aBase p + e < nS p := by simp only [nS, aBase]; omega
  refine ⟨⟨c', by rw [keepB hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs), h.rs],
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    fun hk => (h.fam hk).keep hp ps (by decide) fr (by omega) (by ofs), h.bad⟩, heax, fun hy => ?_, fun hn => ?_⟩
  · rw [hy] at heax; simp only [↓reduceIte] at heax
    refine ⟨hred heax, ?_⟩
    rw [rej_val hout heax (F.rejMax _ hy)]
    rfl
  · rw [hn] at heax
    rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
    · rw [heax] at h1; cases h1
    · exact h0

/-- `OK ← OK ∧ eax` after the call of entry `e`. -/
theorem rejAnd_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (RB p F.rejF e) (IA p F.rejF (e + 1)) (.block andOK) := by
  refine blk_piece (fun _ _ _ h => h.ia.ctx) (fun s₀ s hp h => wp_andOK hp h.ia.ctx ps fun s' c' fr ok' => ?_) rfl
  have hj : aBase p + e < nS p := by simp only [nS, aBase]; omega
  have fr' := fr0 hp (N := 80) (by decide) fr
  have hfam : okE p F.rejF s₀ e = true → Fam s₀ s'.mem (aBase p) e (aVal p s₀) := fun hk =>
    (h.ia.fam hk).keep hp ps (by decide) fr' (by omega) (by ofs)
  refine ⟨c', by rw [keepB hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofs), h.ia.rs], ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [ok', h.ia.ok, h.eax, and01, okE_succ]
  · rw [okE_succ, Bool.and_eq_true] at hk
    exact (hfam hk.1).snoc (keepP hp ps (by decide) fr' hj (by ofs) (h.yes hk.2))
  · rw [okE_succ, Bool.and_eq_false_iff] at hk
    rcases hk with hk | hk
    · obtain ⟨e', he', hn⟩ := h.ia.bad hk
      exact ⟨e', by omega, hn⟩
    · exact ⟨e, by omega, h.no hk⟩

theorem aP_slot {e : Nat} : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  rw [aP_eq, Nat.div_add_mod]

/-- Entry `e` of `Â`. -/
theorem sampleE_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (e : Nat) (he : e < p.k * p.ℓ) :
    SP p (IA p F.rejF e) (IA p F.rejF (e + 1)) (sampleE P p e) := by
  unfold sampleE rejAt
  rw [aP_slot]
  exact (seedBlk_piece F ps e he).seq ((rejCall_piece F ps e he).seq (rejAnd_piece F ps e he))

/-- `ρ` to `RS`, and `Â`. -/
theorem expandA_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ scw s₀ s oOK = 1) (IA p F.rejF (p.k * p.ℓ)) (Impl.MlDsa.X86.Sign.expandA P p) := by
  unfold Impl.MlDsa.X86.Sign.expandA
  refine Piece.seq (B := IA p F.rejF 0) (copy_piece 0 0 SC oRS 8 (by decide) (by decide) (by ofs)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ?_)
    (by simpa using seqR_piece (I := IA p F.rejF) 0 (p.k * p.ℓ) fun e _ he => sampleE_piece F ps e (by omega))
  have fr' : Frame (FR s₀ [sc oRS 32] 80) s.mem s'.mem := fr.mono (by simp)
  refine ⟨c', ?_, ?_, fun _ j hj => absurd hj (Nat.not_lt_zero _), fun hk => absurd hk (by simp [okE])⟩
  · show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oRS, 4 * 8⟩) (4 * 8) = _
    rw [hb, h.1.roBytes hp (b := ⟨0, 0, 4 * 8⟩) (by ofs) rfl]
    exact (VG.Proof.MlKem.bytesAt_take _ _ (skLen_ge ps)).symm
  · rw [scw, keepW' hp (by decide) fr' (sc_ok' ps (by decide) (by decide)) (by ofs)]
    simp [okE, h.2]

end VG.Proof.MlDsa.X86.Sign
