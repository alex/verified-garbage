import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimA
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimD
import VerifiedGarbage.Proof.MlDsa.Sample.Hash

/-!
# ML-DSA signing on x86 (32-bit): the private key, and `ρ″`

Untrusted: everything here is checked by Lean. `ŝ₁`, `ŝ₂` and `t̂₀` are the
`NTT` of the `BitUnpack` of their pieces of `sk` (`decOne_piece`), in the
slots from `s1B`, `s2B` and `t0B`, next to `Â` (`DK`); then `K ‖ rnd` is
copied to `HIN`, and `ρ″ = H(K ‖ rnd ‖ μ, 64)` hashed to `MS` (`KD`).
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

/-- The values of `ŝ₁`, `ŝ₂` and `t̂₀`, from the initial state. -/
abbrev S1 (s₀ : State) : Nat → Poly := s1F p (skOf p s₀)
abbrev S2 (s₀ : State) : Nat → Poly := s2F p (skOf p s₀)
abbrev T0 (s₀ : State) : Nat → Poly := t0F p (skOf p s₀)

/-- `ρ″`, from the initial state. -/
abbrev rppS (s₀ : State) : List Byte := rppV (skOf p s₀) (muOf s₀) (rndOf s₀)

/-- `Â`, and the first `n1`, `n2` and `n0` polynomials of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
structure DK (n1 n2 n0 : Nat) (s₀ : State) (m : Mem) : Prop where
  fa : Fam s₀ m (aBase p) (p.k * p.ℓ) (aVal p s₀)
  f1 : Fam s₀ m (s1B p) n1 (S1 p s₀)
  f2 : Fam s₀ m (s2B p) n2 (S2 p s₀)
  f0 : Fam s₀ m (t0B p) n0 (T0 p s₀)

/-- What the loop needs of the setup. -/
structure KD (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  dk : DK p p.ℓ p.k p.k s₀ s.mem
  ms : bytesAt s.mem (Buf.addr s₀ (sc oMS 64)) 64 = rppS p s₀

end

theorem DK.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {n1 n2 n0 : Nat} (h1 : n1 ≤ p.ℓ) (h2 : n2 ≤ p.k)
    (h0 : n0 ≤ p.k) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : ∀ c ∈ bs, OutK p n1 n2 n0 c) (d : DK p n1 n2 n0 s₀ m) : DK p n1 n2 n0 s₀ m' :=
  ⟨d.fa.keep hp ps hN fr (by simp only [nS, aBase]; omega) fun c hc => (h c hc).1,
    d.f1.keep hp ps hN fr (by simp only [nS, s1B]; omega) fun c hc => (h c hc).2.1,
    d.f2.keep hp ps hN fr (by simp only [nS, s2B]; omega) fun c hc => (h c hc).2.2.1,
    d.f0.keep hp ps hN fr (by simp only [nS, t0B]; omega) fun c hc => (h c hc).2.2.2⟩

/-! ## A polynomial of the private key -/

/-- The bytes `sk[o : o + l]`. -/
theorem sk_slice {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o l : Nat} (hol : o + l ≤ p.skLen)
    (hl : 0 < l) : bytesAt s.mem (Buf.addr s₀ (bSk o l)) l = ((skOf p s₀).drop o).take l := by
  have ok : (Y p).ok (bSk o l) = true :=
    Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), hl, by rw [Y_alen0]; exact hol⟩
  have ok0 : (Y p).ok (bSk 0 p.skLen) = true :=
    Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), by show 0 < p.skLen; omega,
      by rw [Y_alen0]; show 0 + p.skLen ≤ p.skLen; omega⟩
  rw [h.roBytes hp ok rfl, VG.Proof.MlKem.bytesAt_slice _ _ hol, Buf.addr_eq hp ok, Buf.addr_eq hp ok0]
  simp only [BitVec.add_zero]

/-- `f ← NTT(BitUnpack(sk[o : o + len], a, b))`, in slot `j`. -/
theorem decOne_piece {P : Prims} (F : PrimsOk P) (ps : PS p) {A B : State → State → Prop} (j o len a b : Nat)
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32)
    (hj : j < nS p) (hol : o + len ≤ p.skLen) (hlen : 0 < len)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ (pS j)) (ntt (toRq (bitUnpack (((skOf p s₀).drop o).take len) a b))) → B s₀ s') :
    SP p A B (.seq (bitUnpackAt P (bSk o len) a b (pS j)) (nttAt P (pS j))) := by
  have hc : ((Y p).ok ⟨0, o, len⟩ && (Y p).okW ⟨SC, oP j, 1024⟩ && (Y p).sep ⟨0, o, len⟩ ⟨SC, oP j, 1024⟩) = true := by
    have := slot_ok ps hj
    simp only [Bool.and_eq_true, this, and_true]
    exact ⟨Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 0 < 5), hlen, by rw [Y_alen0]; exact hol⟩, Lay.sep_iff.mpr (.inr ⟨by simp, .inr rfl⟩)⟩
  refine Piece.seq (B := fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ Frame (FR s₀ [pS j, sc oPS 1024] 80) s.mem s₁.mem ∧
      PolyIs s₁.mem (Buf.addr s₀ (pS j)) (toRq (bitUnpack (((skOf p s₀).drop o).take len) a b)))
    (bu_piece F.bitUnpack (F.ok _ (by simp)) a b len hab hl hs 0 o SC (oP j) hc hA
      fun s₀ s s' hp ha c' fr hq => ⟨s, ha, c', fr.mono (by simp), by rw [← sk_slice hp (hA _ _ hp ha) hol hlen]; exact hq⟩) ?_
  refine inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) (pS j) rfl (by
      have := slot_ok ps hj; have := sc_ok ps (o := oPS) (n := 1024) (by decide) (by decide)
      simp only [Bool.and_eq_true, *, true_and]; ofs)
    (fun s₀ s₁ hp ⟨_, _, c, _, hq⟩ => ⟨c, hq.1⟩) fun s₀ s₁ s' hp ⟨s, ha, c, fr, hq⟩ c' fr' post => ?_
  rw [hq.2] at post
  exact hQ s₀ s s' hp ha c' (fr.trans fr') post

/-! ## The private key -/

theorem ps_sk (ps : PS p) : sLen p * p.ℓ + sLen p * p.k + 416 * p.k + 128 = p.skLen := by
  rw [ps.hskLen, Nat.mul_add]; omega

theorem ps_sLen (ps : PS p) : 0 < sLen p ∧ sLen p < 2 ^ 32 := by rcases ps.hsLen with h | h <;> omega

/-- `ŝ₁`. -/
theorem decS1s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p 0 0 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ 0 0 s₀ s.mem)
      (seqR (decS1 P p) 0 p.ℓ) := by
  have := seqR_piece (p := p) (f := decS1 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DK p r 0 0 s₀ s.mem) 0 p.ℓ
    fun r _ hr => by
      have hl := ps_sLen ps
      have hk := ps_sk ps
      have hr' : r < p.ℓ := by omega
      have hmul : sLen p * r + sLen p ≤ sLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact decOne_piece F ps (s1B p + r) (skS1 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [nS, s1B]; omega) (by simp only [skS1]; omega) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (by omega) (by omega) (by omega) (by decide) fr (by ofs)) with
            f1 := (h.2.f1.keep hp ps (by decide) fr (by simp only [nS, s1B]; omega) (by ofs)).snoc hq }⟩
  simpa using this

/-- `ŝ₂`. -/
theorem decS2s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ 0 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k 0 s₀ s.mem)
      (seqR (decS2 P p) 0 p.k) := by
  have := seqR_piece (p := p) (f := decS2 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ r 0 s₀ s.mem) 0 p.k
    fun r _ hr => by
      have hl := ps_sLen ps
      have hk := ps_sk ps
      have hr' : r < p.k := by omega
      have hmul : sLen p * r + sLen p ≤ sLen p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      exact decOne_piece F ps (s2B p + r) (skS2 p r) (sLen p) p.η p.η ps.hη.1 ps.hη.2.1
        ⟨ps.hη.2.2, ps.hη.2.2, hl.2⟩ (by simp only [nS, s2B]; omega) (by simp only [skS2]; omega) hl.1
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (by omega) (by omega) (by decide) fr (by ofs)) with
            f2 := (h.2.f2.keep hp ps (by decide) fr (by simp only [nS, s2B]; omega) (by ofs)).snoc hq }⟩
  simpa using this

theorem t0F_eq (sk : List Byte) (i : Nat) :
    t0F p sk i = ntt (toRq (bitUnpack ((sk.drop (skT0 p i)).take 416) 4095 4096)) := by
  unfold t0F
  rw [show 128 + lenS p * p.ℓ + lenS p * p.k + 32 * d * i = skT0 p i by
    simp only [skT0, lenS, sLen, Nat.mul_add, d]; omega]
  rfl

/-- `t̂₀`. -/
theorem decT0s_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k 0 s₀ s.mem) (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem)
      (seqR (decT0 P p) 0 p.k) := by
  have := seqR_piece (p := p) (f := decT0 P p) (I := fun r s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k r s₀ s.mem) 0 p.k
    fun r _ hr => by
      have hk := ps_sk ps
      have hr' : r < p.k := by omega
      have hmul : 416 * r + 416 ≤ 416 * p.k := by omega
      exact decOne_piece F ps (t0B p + r) (skT0 p r) 416 4095 4096 ps.ht0.1 ps.ht0.2
        ⟨by decide, by decide, by decide⟩ (by simp only [nS, t0B]; omega) (by simp only [skT0, Nat.mul_add]; omega) (by decide)
        (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hq => ⟨c',
          { (h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (by omega) (by decide) fr (by ofs)) with
            f0 := (h.2.f0.keep hp ps (by decide) fr (by simp only [nS, t0B]; omega) (by ofs)).snoc
              (by show PolyIs _ _ (t0F p _ r); rw [t0F_eq]; exact hq) }⟩
  simpa using this

/-! ## `ρ″` -/

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`, with `K ‖ rnd` copied to `HIN` first. -/
theorem rpp_piece (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem) (KD p)
      (.seq (copyW SC (bSk 32 32) (sc oHIN 32) 8) (.seq (copyW SC bRnd (sc (oHIN + 32) 32) 8)
        (shake2 (sc oHIN 64) bMu (sc oMS 64)))) := by
  have hk := ps_sk ps
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 32)) 32 = ((skOf p s₀).drop 32).take 32)
    (copy_piece 0 32 SC oHIN 8 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc oHIN 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofs), by
          show bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN, 4 * 8⟩) (4 * 8) = _
          rw [hb]; exact sk_slice hp h.1 (by omega) (by decide)⟩) ?_
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ DK p p.ℓ p.k p.k s₀ s.mem ∧
      bytesAt s.mem (Buf.addr s₀ (sc oHIN 64)) 64 = ((skOf p s₀).drop 32).take 32 ++ rndOf s₀)
    (copy_piece 2 0 SC (oHIN + 32) 8 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (N := 80)
        (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp)) (by ofs), by
          rw [bytes_split hp s'.mem (o' := oHIN + 32) (l₁ := 32) (l₂ := 32) rfl rfl (sc_ok' ps (by decide) (by decide))
            (sc_ok' ps (by decide) (by decide)), keepB hp (N := 80) (by decide) (show Frame (FR s₀ [sc (oHIN + 32) 32] 80) s.mem s'.mem from fr.mono (by simp))
            (sc_ok' ps (by decide) (by decide)) (by ofs), h.2.2]
          have : bytesAt s'.mem (Buf.addr s₀ ⟨SC, oHIN + 32, 4 * 8⟩) (4 * 8) = _ := hb
          rw [this, h.1.roBytes hp (b := ⟨2, 0, 4 * 8⟩) (by ofs) rfl]⟩) ?_
  refine hash2_piece' 136 0x1f (sc oHIN 64) bMu (sc oMS 64) (by decide) (by ofs) (by decide) (by decide) (by decide)
    (fun _ _ _ h => h.1) fun s₀ s s' hp h c' fr hb => ⟨c', h.2.1.keep hp ps (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (by decide) fr (by ofs), ?_⟩
  have e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  rw [hb, h.2.2, h.1.roBytes hp (b := bMu) (by ofs) rfl, e, rppS, rppV, VG.Proof.MlDsa.Sample.H_eq]

/-- The setup after `ExpandA`. -/
theorem decode_piece {P : Prims} (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => Ctx (Y p) s₀ s ∧ DK p 0 0 0 s₀ s.mem) (KD p) (decode P p) :=
  (decS1s_piece F ps).seq ((decS2s_piece F ps).seq ((decT0s_piece F ps).seq (rpp_piece ps)))

end VG.Proof.MlDsa.X86.Sign
