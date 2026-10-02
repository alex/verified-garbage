import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimC

/-!
# ML-DSA signing on x86 (32-bit): the commitment of an iteration

Iteration `t` of the loop (`IT`: the setup, `κ = ℓt` at `KAP` and `814 - t` at
`CNT`) computes `y = ExpandMask(ρ″, κ)` and `ŷ = NTT(y)` (`maskR_piece`), `w =
NTT⁻¹(Â ŷ)` (`rowW_piece`), the encoding of `w₁ = HighBits(w)` at `W1`
(`w1R_piece`), and `c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at `CT` (`commit_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

section
variable (p : Params)

/-- `Â`, `y`, `ŷ`, `w` and `c̃` of the iteration with counter `κ`. -/
abbrev Am (s₀ : State) : Nat → Nat → Poly := Av (skOf p s₀)
abbrev Yv (s₀ : State) (κ r : Nat) : Poly := toRq (yF p (rppS p s₀) κ r)
abbrev YHv (s₀ : State) (κ r : Nat) : Poly := yhF p (rppS p s₀) κ r
abbrev Wv (s₀ : State) (κ i : Nat) : Poly := wF p (Am p s₀) (rppS p s₀) κ i
abbrev CTv (s₀ : State) (κ : Nat) : List Byte := ctF p (Am p s₀) (muOf s₀) (rppS p s₀) κ

/-- Iteration `t`, on entry. -/
structure IT (t : Nat) (s₀ s : State) : Prop where
  kd : KD p s₀ s
  kap : scw s₀ s oKAP = BitVec.ofNat 32 (p.ℓ * t)
  cnt : scw s₀ s oCNT = BitVec.ofNat 32 (814 - t)
  lt : t < 814

end

theorem IT.keep {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : IT p t s₀ s)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutI p c) : IT p t s₀ s' :=
  ⟨⟨c', h.kd.dk.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hN fr fun c hc => (hb c hc).1,
    by rw [keepB hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2, h.kd.ms]⟩,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega⟩]; exact h.kap,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).2.1.1, fun e => by
      have := (hb c hc).2.1.2 e; simp only [oCNT, oKAP] at this ⊢; omega⟩]; exact h.cnt, h.lt⟩

theorem aVal_ij {s₀ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p s₀ (p.ℓ * i + j) = Am p s₀ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, e1, e2]

/-! ## `y` and `ŷ` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kap_lt (ps : PS p) {t r : Nat} (ht : t < 814) (hr : r < p.ℓ) : p.ℓ * t + r < 2 ^ 16 := by
  have := ps.hl
  have : p.ℓ * t ≤ 7 * 813 := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure CM (p : Params) (t r : Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  fy : Fam s₀ s.mem (yB p) r (Yv p s₀ (p.ℓ * t))
  fyh : Fam s₀ s.mem (yhB p) r (YHv p s₀ (p.ℓ * t))

/-- `κ + r` to `MS + 64`: the seed of `y[r]` at `MS`. -/
theorem setKappa_piece (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CM p t r) (fun s₀ s => CM p t r s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sc oMS 66)) 66 = rppS p s₀ ++ integerToBytes (p.ℓ * t + r) 2)
      (.block (setKappa r)) := by
  refine blk_piece (fun _ _ _ h => h.it.kd.ctx) (fun s₀ s hp hc => ?_) rfl
  have h := hc.it
  have hk := kap_lt ps h.lt hr
  unfold setKappa
  refine wp_ldsc hp h.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addi fun s₂ o₂ v₂ => ?_
  have c₂ := h.kd.ctx.only (o₁.trans o₂) (by simp) (by simp)
  refine wp_st8sc hp c₂ (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ => wp_shr (by decide) (by decide)
    fun s₄ o₄ v₄ => ?_
  have c₄ := c₃.only o₄ (by simp) (by simp)
  refine wp_st8sc hp c₄ (sc_ok ps (by decide) (by decide)) fun s₅ c₅ g₅ m₅ => WP.block_nil_iff.mpr ?_
  have ex : s₂.gpr .eax = BitVec.ofNat 32 (p.ℓ * t + r) := by
    rw [v₂, v₁, h.kap, BitVec.ofNat_add]
  have fr₃ : Frame (FR s₀ [sc (oMS + 64) 1] 0) s.mem s₃.mem := by
    rw [m₃, ← (o₁.trans o₂).mem]; exact frW8 (Y := Y p)
  have fr₅ : Frame (FR s₀ [sc (oMS + 65) 1] 0) s₃.mem s₅.mem := by
    rw [m₅, ← o₄.mem]; exact frW8 (Y := Y p)
  have fs : ∀ o, o = oMS + 64 ∨ o = oMS + 65 → ∀ c ∈ [sc o 1], c.arg = SC ∧ oMS + 64 ≤ c.off ∧
      c.off + c.len ≤ oMS + 66 ∧ 0 < c.len :=
    fun o ho c hc => by rw [List.mem_singleton] at hc; subst hc; simp only [oMS, true_and] at ho ⊢; omega
  have hhi : oMS + 66 ≤ scrLen p := by have := scr_ge ps; simp only [oP, oMS, nS] at this ⊢; omega
  have f := (frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inl rfl)) fr₃).trans
    (frSc hp (M := 80) (by decide) (by decide) (by decide) hhi (fs _ (.inr rfl)) fr₅)
  refine ⟨⟨h.keep hp ps c₅ (by decide) f (by ofs), hc.fy.keep hp ps (by decide) f (by simp only [nS, yB]; omega) (by ofs),
    hc.fyh.keep hp ps (by decide) f (by simp only [nS, yhB]; omega) (by ofs)⟩, ?_⟩
  have b0 : bytesAt s₃.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [m₃, bytes1_write]; show [(s₂.gpr .eax).setWidth 8] = _; rw [ex, setWidth8_ofNat]
  have b0' : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 64) 1)) 1 = [BitVec.ofNat 8 (p.ℓ * t + r)] := by
    rw [keepB hp (by decide) fr₅ (sc_ok' ps (by decide) (by decide)) fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨sc_ok' ps (by decide) (by decide), fun _ => .inr (Nat.le_refl _)⟩, b0]
  have b1 : bytesAt s₅.mem (Buf.addr s₀ (sc (oMS + 65) 1)) 1 = [BitVec.ofNat 8 ((p.ℓ * t + r) / 256)] := by
    rw [m₅, bytes1_write]; show [(s₄.gpr .eax).setWidth 8] = _; rw [v₄, g₃, ex]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega
  have hm : bytesAt s₅.mem (Buf.addr s₀ (sc oMS 64)) 64 = rppS p s₀ := by
    rw [keepB hp (by decide) f (sc_ok' ps (by decide) (by decide)) (by ofs), h.kd.ms]
  rw [bytes_split hp s₅.mem (o' := oMS + 64) (l₁ := 64) (l₂ := 2) rfl rfl (sc_ok' ps (by decide) (by decide))
    (sc_ok' ps (by decide) (by decide)), hm,
    bytes_split hp s₅.mem (o' := oMS + 65) (l₁ := 1) (l₂ := 1) rfl rfl (sc_ok' ps (by decide) (by decide))
    (sc_ok' ps (by decide) (by decide)), b0', b1, integerToBytes_two]
  rfl

/-- `y[r]` and `ŷ[r]`. -/
theorem maskR_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CM p t r) (CM p t (r + 1)) (maskR P p r) := by
  have hj : yB p + r < nS p := by simp only [nS, yB]; omega
  have hj' : yhB p + r < nS p := by simp only [nS, yhB]; omega
  refine (setKappa_piece ps t r hr).seq ?_
  refine Piece.seq (B := fun s₀ s => CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (yB p + r))) (Yv p s₀ (p.ℓ * t) r))
    (mask_piece F.expandMask (F.ok _ (by simp)) p.γ₁ ps.hγ₁ SC oMS SC (oP (yB p + r)) SC oPS (by ofs)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hq => ⟨⟨h.1.it.keep hp ps c' (by decide) fr (by ofs),
        h.1.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega) (by ofs),
        h.1.fyh.keep hp ps (by decide) fr (by simp only [nS, yhB]; omega) (by ofs)⟩, by rw [h.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CM p t r s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (yB p + r))) (Yv p s₀ (p.ℓ * t) r) ∧
      PolyIs s.mem (Buf.addr s₀ (pS (yhB p + r))) (Yv p s₀ (p.ℓ * t) r))
    (copy_piece SC (oP (yB p + r)) SC (oP (yhB p + r)) 256 (by decide) (by decide) (by ofs)
      (fun _ _ _ h => h.1.it.kd.ctx) fun s₀ s s' hp h c' fr hb => ?_) ?_
  · have fr' : Frame (FR s₀ [pS (yhB p + r)] 80) s.mem s'.mem := fr.mono (by simp)
    exact ⟨⟨h.1.it.keep hp ps c' (by decide) fr' (by ofs),
      h.1.fy.keep hp ps (by decide) fr' (by simp only [nS, yB]; omega) (by ofs),
      h.1.fyh.keep hp ps (by decide) fr' (by simp only [nS, yhB]; omega) (by ofs)⟩,
      keepP hp ps (by decide) fr' hj (by ofs) h.2, polyIs_of_bytes hb h.2⟩
  refine inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) (pS (yhB p + r)) rfl (by ofs)
    (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2.2] at hq
  exact ⟨h.1.it.keep hp ps c' (by decide) fr (by ofs),
    (h.1.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega) (by ofs)).snoc (keepP hp ps (by decide) fr hj (by ofs) h.2.1),
    (h.1.fyh.keep hp ps (by decide) fr (by simp only [nS, yhB]; omega) (by ofs)).snoc hq⟩

/-! ## `w` -/

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (s₀ : State) (κ i m : Nat) : Poly :=
  ((List.range m).map fun j => multiplyNTT (Am p s₀ i j) (YHv p s₀ κ j)).foldl add zero

theorem add_zero_left (x : Poly) : add zero x = x := by
  apply Vector.ext
  intro j hj
  simp [add, zero]

theorem wAcc_one (s₀ : State) (κ i : Nat) :
    wAcc p s₀ κ i 1 = multiplyNTT (Am p s₀ i 0) (YHv p s₀ κ 0) := by
  simp only [wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, add_zero_left]

theorem wAcc_succ (s₀ : State) (κ i m : Nat) :
    wAcc p s₀ κ i (m + 1) = add (wAcc p s₀ κ i m) (multiplyNTT (Am p s₀ i m) (YHv p s₀ κ m)) := by
  simp only [wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Iteration `t`, with `y`, `ŷ` and the first `i` polynomials of `w`. -/
structure CW (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cm : CM p t p.ℓ s₀ s
  fw : Fam s₀ s.mem (wB p) i (Wv p s₀ (p.ℓ * t))

theorem CW.keep {t i : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CW p t i s₀ s) (hi : i ≤ p.k)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, OutI p c ∧ Out p (oP (yB p)) (oP (wB p + i)) c) : CW p t i s₀ s' :=
  ⟨⟨h.cm.it.keep hp ps c' hN fr fun c hc => (hb c hc).1,
    h.cm.fy.keep hp ps hN fr (by simp only [nS, yB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, wB] at this ⊢; omega⟩,
    h.cm.fyh.keep hp ps hN fr (by simp only [nS, yhB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, yhB, wB] at this ⊢; omega⟩⟩,
    h.fw.keep hp ps hN fr (by simp only [nS, wB]; omega) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oP, yB, wB] at this ⊢; omega⟩⟩

theorem fam_at {s₀ : State} {m : Mem} {b n : Nat} {f : Nat → Poly} (h : Fam s₀ m b n f) {j : Nat} (hj : j < n) :
    PolyIs m (Buf.addr s₀ (pS (b + j))) (f j) := h j hj

/-- `w[i]`. -/
theorem rowW_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CW p t i) (CW p t (i + 1)) (rowW P p i) := by
  have hl := ps.hl
  have hj : wB p + i < nS p := by simp only [nS, wB]; omega
  have ha : ∀ j < p.ℓ, p.ℓ * i + j < p.k * p.ℓ := fun j hj => aIdx hi hj
  unfold rowW
  simp only [aP_eq]
  refine Piece.seq (B := fun s₀ s => CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i 1))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP (aBase p + (p.ℓ * i + 0))) SC (oP (yhB p + 0))
      (by have := ha 0 (by omega); ofs)
      (fun _ _ _ h => ⟨h.cm.it.kd.ctx, (fam_at h.cm.it.kd.dk.fa (ha 0 (by omega))).1, (fam_at h.cm.fyh (by omega)).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps (by omega) c' (by decide) fr (by ofs), ?_⟩) ?_
  · rw [(fam_at h.cm.it.kd.dk.fa (ha 0 (by omega))).2, (fam_at h.cm.fyh (by omega)).2, aVal_ij (by omega)] at hq
    rw [wAcc_one]; exact hq
  refine Piece.seq (B := fun s₀ s => CW p t i s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i p.ℓ))
    ?_ ?_
  · have := seqR_piece (p := p) (I := fun j s₀ s => CW p t i s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS (wB p + i))) (wAcc p s₀ (p.ℓ * t) i j)) 1 (p.ℓ - 1) fun j hj1 hj2 =>
      mulAdd_piece (nm := "vg_mldsa_multiply_add_ntt") F.mulAdd (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP (aBase p + (p.ℓ * i + j))) SC (oP (yhB p + j))
        (by have := ha j (by omega); ofs)
        (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1, (fam_at h.1.cm.it.kd.dk.fa (ha j (by omega))).1,
          (fam_at h.1.cm.fyh (by omega)).1⟩)
        fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps (by omega) c' (by decide) fr (by ofs), by
          rw [h.2.2, (fam_at h.1.cm.it.kd.dk.fa (ha j (by omega))).2, (fam_at h.1.cm.fyh (by omega)).2,
            aVal_ij (by omega)] at hq
          rw [wAcc_succ]; exact hq⟩
    rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at this
  refine inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) (pS (wB p + i)) rfl (by ofs)
    (fun _ _ _ h => ⟨h.1.cm.it.kd.ctx, h.2.1⟩) fun s₀ s s' hp h c' fr hq => ?_
  rw [h.2.2] at hq
  exact ⟨(h.1.keep hp ps (by omega) c' (by decide) fr (by ofs)).cm, (h.1.keep hp ps (by omega) c' (by decide) fr
    (by ofs)).fw.snoc hq⟩

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (s₀ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (Am p s₀) (rppS p s₀) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure CH (p : Params) (t i : Nat) (s₀ s : State) : Prop where
  cw : CW p t p.k s₀ s
  w1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 1024)) (w1Len p * i) = w1Enc p s₀ (p.ℓ * t) i

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

/-- `w1Encode(w₁[i])` to `W1 + w1Len · i`. -/
theorem w1R_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CH p t i) (CH p t (i + 1)) (w1R P p i) := by
  have hj : wB p + i < nS p := by simp only [nS, wB]; omega
  have hw := ps.hw1
  have hwl : w1Len p * i + w1Len p ≤ 1024 := by
    have : w1Len p * i + w1Len p ≤ w1Len p * p.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [Nat.mul_comm p.k] at hw; omega
  have hwp : 0 < w1Len p := by rcases ps.hw1Len with h | h <;> omega
  refine Piece.seq (B := fun s₀ s => CH p t i s₀ s ∧
      NatPolyIs s.mem (Buf.addr s₀ t1P) (w1F p (Am p s₀) (rppS p s₀) (p.ℓ * t) i))
    (hb_piece F.highBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP (wB p + i)) SC (oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.cw.cm.it.kd.ctx, (fam_at h.cw.fw hi).1⟩) fun s₀ s s' hp h c' fr hq =>
      ⟨⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), by
        rw [keepB0 hp (by decide) fr 1024 (by have := scr_ge ps; simp only [oP, oW1, nS] at this ⊢; omega) (by ofs)]
        exact h.w1⟩, by rw [(fam_at h.cw.fw hi).2] at hq; exact hq⟩) ?_
  refine sbp_piece F.simpleBitPack (F.ok _ (by simp)) (w1Max p) (w1Len p) ps.hw1Max.1 ps.hw1Max.2 SC (oP 1) SC
    (oW1 + w1Len p * i) (by ofs) (fun _ _ _ h => ⟨h.1.cw.cm.it.kd.ctx, fun j hj => by
      rw [natPolyIs_coeff h.2 hj, w1F, Vector.getElem_map]; exact highBits_le ps.hγ₂ _⟩)
    fun s₀ s s' hp h c' fr hq => ⟨h.1.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), ?_⟩
  have e : Buf.addr s₀ (sc (oW1 + w1Len p * i) (w1Len p)) = Buf.addr s₀ (sc oW1 1024) + BitVec.ofNat 64 (w1Len p * i) :=
    addr_off hp (sc_ok' ps (by decide) (by decide)) (by ofs)
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, ← e, hq, h.2,
    keepB0 hp (by decide) fr 1024 (by have := scr_ge ps; simp only [oP, oW1, nS] at this ⊢; omega) (by ofs), h.1.w1,
    w1Enc, w1Enc, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Iteration `t`, with `y`, `w` and `c̃`. -/
structure CC (p : Params) (t : Nat) (s₀ s : State) : Prop where
  cw : CW p t p.k s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)

theorem w1Enc_eq (s₀ : State) (κ : Nat) :
    w1Enc p s₀ κ p.k = w1Encode p ((List.range p.k).map (w1F p (Am p s₀) (rppS p s₀) κ)) := by
  simp only [w1Enc, w1Encode, List.flatMap_map]

/-- The commitment of iteration `t`. -/
theorem commit_piece {P : Prims} (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (CM p t 0) (CC p t) (commit P p) := by
  have hw := ps.hw1
  have hc := ps.hcLen
  refine Piece.seq (B := CM p t p.ℓ) ?_ ?_
  · have := seqR_piece (p := p) (I := CM p t) 0 p.ℓ fun r _ hr => maskR_piece F ps t r (by omega)
    simpa using this
  refine Piece.seq (B := CW p t p.k) ?_ ?_
  · have := seqR_piece (p := p) (I := CW p t) 0 p.k fun i _ hi => rowW_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun _ _ _ h => h
  refine Piece.seq (B := CH p t p.k) ?_ ?_
  · have := seqR_piece (p := p) (I := CH p t) 0 p.k fun i _ hi => w1R_piece F ps t i (by omega)
    simp only [Nat.zero_add] at this
    exact this.mono (fun _ _ _ h => ⟨h, rfl⟩) fun _ _ _ h => h
  refine hash2_piece' 136 0x1f bMu (sc oW1 (p.k * w1Len p)) (sc oCT (cLen p)) (by decide) (by ofs) (by decide)
    (by show p.k * w1Len p < 2 ^ 32; omega) (by show cLen p < 2 ^ 32; omega) (fun _ _ _ h => h.cw.cm.it.kd.ctx)
    fun s₀ s s' hp h c' fr hb => ⟨h.cw.keep hp ps (Nat.le_refl _) c' (by decide) fr (by ofs), ?_⟩
  have e : BitVec.setWidth 8 (31#32) = Spec.Sha3.shakeSuffix := by decide
  have hw1 : bytesAt s.mem (Buf.addr s₀ (sc oW1 (p.k * w1Len p))) (p.k * w1Len p) = w1Enc p s₀ (p.ℓ * t) p.k := by
    rw [Nat.mul_comm]; exact h.w1
  simp only [sc, bMu] at hb hw1 ⊢
  rw [hb, hw1, h.cw.cm.it.kd.ctx.roBytes hp (b := bMu) (by ofs) rfl, e, w1Enc_eq, CTv, ctF,
    VG.Proof.MlDsa.Sample.H_eq]

end VG.Proof.MlDsa.X86.Sign
