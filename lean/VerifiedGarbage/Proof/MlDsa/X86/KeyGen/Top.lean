import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp

/-!
# ML-DSA key generation on x86 (32-bit): `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

Untrusted: everything here is checked by Lean. The body, piece by piece
(`body_piece`), for any parameter set of Table 1 and any verified
implementations of the primitives: it returns 1 with `KeyGen_internal(ξ)` in
`pk` and `sk` if every sampler succeeded (for some bounds), and 0 if key
generation fails within the least bounds (`post`); it leaks only the
pointers, `ρ` and what `RejBoundedPoly` leaks; so the function meets the
shared contract (`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## `tr = H(pk, 64)`, and the value returned -/

/-- At the end: the keys, and the value returned. -/
structure KFin (p : Params) (s₀ s : State) : Prop where
  ex : ∃ A S, KR p A S (p.ℓ + p.k) p.ℓ p.k s₀ s ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen) 64

theorem trHash_piece {p : Params} (hF : PFacts p) : KP p (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) (trHash p) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  refine hash1_piece (Y := YK p) 0 200 136 0x1f ⟨1, 0, p.pkLen⟩ ⟨2, 64, 64⟩ Proof.MlKem.rate136 (by layp hF)
    (by rw [YK_stk]; omega) (by show p.pkLen < 2 ^ 32; rw [hF.pk]; omega) (by decide) (by taint_decide) (h₁ := .block [])
    (by kernel_rfl) (h₃ := .block []) (by kernel_rfl) (h₄ := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, h⟩ => h.ctx) fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_, ?_⟩
  · exact h.keep hp (N := 40) (by omega) (by safeR hF) (fun _ _ => by layp hF) fr h'
  · rw [out, sponge_H, keepBytes hp (N := 40) (stkN (by omega)) (b := ⟨1, 0, p.pkLen⟩) (by layp hF) fr]

/-- The body's end: the keys, and `eax` the AND of the samplers' results. -/
structure Done (p : Params) (s₀ s : State) : Prop extends KFin p s₀ s where
  eax : s.gpr .eax = accV s₀ s

theorem ret_piece {p : Params} (hF : PFacts p) :
    KP p (KFin p) (fun s₀ s => Ctx (YK p) s₀ s ∧ Done p s₀ s) (.block [.mov .eax (.mem (at_ .esi oACC))]) := by
  refine ld32_piece (Y := YK p) oACC (by layp hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => by obtain ⟨_, _, h, _⟩ := h.ex; exact h.ctx) fun s₀ s s' hp h h' m' e => ⟨h', ?_, ?_⟩
  · obtain ⟨A, S, hk, htr⟩ := h.ex
    exact ⟨A, S, hk.keep hp (bs := []) (N := 0) (by omega) (by safeR hF) (fun _ _ => by layp hF) (by rw [m']; exact Frame.refl _ _)
      h', by rw [m']; exact htr⟩
  · rw [e, accV, m']; rfl

/-! ## The body -/

theorem body_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    KP p (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx (YK p) s₀ s ∧ Done p s₀ s) (body P p) := by
  have hk := hF.k; have hl := hF.l
  unfold body
  refine (ldsc_piece (Y := YK p) (ht := .block []) (by kernel_rfl)).seq ((seeds_piece hF).seq ?_)
  refine Piece.seq (B := KSamp p (p.k * p.ℓ) 0) (Piece.mono (seqR_piece (I := fun e => KSamp p e 0)
    (p.k * p.ℓ) 0 fun e _ he => expA_piece hP hF (by omega)) (fun s₀ s _ h => ⟨h.1, fun _ => Proof.MlDsa.KeyGen.zeroI.map
      (fun _ => 0), fun _ => Proof.MlDsa.KeyGen.zeroI, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), .inl ⟨h.2, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (Piece.mono (seqR_piece
    (I := fun r => KSamp p (p.k * p.ℓ) r) (p.ℓ + p.k) 0 fun r _ hr => expS_piece hP hF (by omega))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine (copies_piece hF).seq ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) 0 0) (Piece.mono (seqR_piece (I := fun r => KRx p r 0 0) (p.ℓ + p.k) 0
    fun r _ hr => packS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) p.ℓ 0) (Piece.mono (seqR_piece (I := fun j => KRx p (p.ℓ + p.k) j 0) p.ℓ 0
    fun j _ hj => nttS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  refine Piece.seq (B := KRx p (p.ℓ + p.k) p.ℓ p.k) (Piece.mono (seqR_piece
    (I := fun i => KRx p (p.ℓ + p.k) p.ℓ i) p.k 0 fun i _ hi => row_piece hP hF (by omega))
    (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (trHash_piece hF).seq (ret_piece hF)

theorem body_nosp {P : Prims} (hP : PrimsOk P) (p : Params) : NoSp (body P p) := by
  unfold body
  refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq
    (NoSp.seqR (fun e => ?_) _ _) (NoSp.seq (NoSp.seqR (fun r => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.seq (NoSp.seqR (fun r => NoSp.callP hP.bitPack.nosp) _ _) (NoSp.seq (NoSp.seqR (fun j =>
      NoSp.callP hP.ntt.nosp) _ _) (NoSp.seq (NoSp.seqR (fun i => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl))
    (NoSp.of_all (by kernel_rfl))))))))))
  · unfold expA
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl))
      (NoSp.seq (NoSp.callPR hP.rejNtt.nosp) (NoSp.of_all (by kernel_rfl))))
  · unfold expS
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.callPR hP.rejBounded.nosp)
      (NoSp.of_all (by kernel_rfl)))
  · unfold row
    exact NoSp.seq (NoSp.callP hP.mul.nosp) (NoSp.seq (NoSp.seqR (fun j => NoSp.callP hP.mulAdd.nosp) _ _)
      (NoSp.seq (NoSp.callP hP.invNtt.nosp) (NoSp.seq (NoSp.callP hP.add.nosp) (NoSp.seq
        (NoSp.callP hP.power2Round.nosp) (NoSp.seq (NoSp.callP hP.simpleBitPack.nosp) (NoSp.callP hP.bitPack.nosp))))))

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

section
variable {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀)
include hF hp

omit hF in
/-- A buffer of `pk` or `sk`, from the start of its argument. -/
theorem addr_arg {a o l : Nat} (h : (YK p).ok ⟨a, o, l⟩ = true) :
    Buf.addr s₀ ⟨a, o, l⟩ = (arg s₀ a).setWidth 64 + BitVec.ofNat 64 o := Buf.addr_eq hp h

theorem pk_bytes {A : Nat → Poly} {S : Nat → IPoly} {np nj : Nat} (h : KR p A S np nj p.k s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen = pkK p A S (rhoOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have e0 := addr_arg hp (a := 1) (o := 0) (l := p.pkLen) (by layp hF)
  have e1 := addr_arg hp (a := 1) (o := 0) (l := 32) (by layp hF)
  rw [BitVec.add_zero] at e0 e1
  rw [hF.pk] at e0 ⊢
  rw [e0, Proof.MlKem.bytesAt_add, ← e1, h.pk0, e1, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK,
    t1Max_eq]
  refine congrArg _ (flatMap_congr_mem fun i hi => ?_)
  have hi := List.mem_range.mp hi
  rw [← addr_arg hp (a := 1) (o := 32 + 320 * i) (l := 320) (by layp hF)]
  exact (h.rows i hi).1

theorem sk_bytes {A : Nat → Poly} {S : Nat → IPoly} {nj : Nat} (h : KR p A S (p.ℓ + p.k) nj p.k s₀ s)
    (htr : bytesAt s.mem (Buf.addr s₀ ⟨2, 64, 64⟩) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p s₀)) 64) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen = skK p A S (rhoOf p s₀) (kOf p s₀) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have a0 := addr_arg hp (a := 2) (o := 0) (l := p.skLen) (by layp hF)
  have a1 := addr_arg hp (a := 2) (o := 0) (l := 32) (by layp hF)
  have a2 := addr_arg hp (a := 2) (o := 32) (l := 32) (by layp hF)
  have a3 := addr_arg hp (a := 2) (o := 64) (l := 64) (by layp hF)
  rw [BitVec.add_zero] at a0 a1
  have h0 : bytesAt s.mem ((arg s₀ 2).setWidth 64) 32 = rhoOf p s₀ := by rw [← a1]; exact h.sk0
  have h1 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 32) 32 = kOf p s₀ := by rw [← a2]; exact h.sk1
  have h2 : bytesAt s.mem ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (32 + 32)) 64 =
      Spec.MlDsa.H (pkK p A S (rhoOf p s₀)) 64 := by rw [← a3]; exact htr
  rw [a0, hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2]
  have p1 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (32 + 32 + 64) (lenS p) (p.ℓ + p.k)
  have p2 := Proof.MlDsa.KeyGen.bytesAt_pieces s.mem ((arg s₀ 2).setWidth 64) (oT0 p) 416 p.k
  rw [oT0] at p2
  have q1 : (List.range (p.ℓ + p.k)).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * i)) (lenS p)) =
      (List.range (p.ℓ + p.k)).flatMap fun r => bitPack (S r) p.η p.η := flatMap_congr_mem fun r hr => by
    rw [← addr_arg hp (a := 2) (o := 32 + 32 + 64 + lenS p * r) (l := lenS p) (by have := List.mem_range.mp hr; layp hF)]
    exact h.packs r (List.mem_range.mp hr)
  have q2 : (List.range p.k).flatMap (fun i => bytesAt s.mem ((arg s₀ 2).setWidth 64 +
      BitVec.ofNat 64 (128 + lenS p * (p.ℓ + p.k) + 416 * i)) 416) =
      (List.range p.k).flatMap fun i => bitPack (t0K p A S i) 4095 4096 := flatMap_congr_mem fun i hi => by
    rw [show 128 + lenS p * (p.ℓ + p.k) = oT0 p from rfl,
      ← addr_arg hp (a := 2) (o := oT0 p + 416 * i) (l := 416) (by have := List.mem_range.mp hi; layp hF)]
    exact (h.rows i (List.mem_range.mp hi)).2
  rw [p1, p2, q1, q2, skK]
  rfl

end

/-! ## The return -/

theorem idx_lt {p : Params} {r s : Nat} (hr : r < p.k) (hs : s < p.ℓ) : p.ℓ * r + s < p.k * p.ℓ := by
  have : p.ℓ * (r + 1) ≤ p.ℓ * p.k := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm p.k]; rw [Nat.mul_succ] at this; omega

theorem outcome_of {p : Params} {s₀ : State} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (hl : 0 < p.ℓ) (hG : Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S v) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf s₀)) v
      (pkK p A S (rhoOf p s₀), skK p A S (rhoOf p s₀) (kOf p s₀)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (xiOf s₀) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem post {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀) (h : Done p s₀ s) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf s₀)) (accV s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, p.pkLen⟩) p.pkLen, bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.skLen⟩) p.skLen) := by
  obtain ⟨A, S, hk, htr⟩ := h.ex
  rw [pk_bytes hF hp hk] at htr
  rw [pk_bytes hF hp hk, sk_bytes hF hp hk htr]
  exact outcome_of (by have := hF.l; omega) hk.good

end VG.Proof.MlDsa.X86.KeyGen
