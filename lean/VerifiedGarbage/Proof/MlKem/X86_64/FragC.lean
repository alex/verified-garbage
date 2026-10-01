import VerifiedGarbage.Proof.MlKem.X86_64.FragS
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM-768 on x86-64: the input of `PRF`, and sums of products

Untrusted: everything here is checked by Lean. In a layout: the input of
`PRF₂(σ, N)` (`prf_pieces`, for `Prfs.lean`), and
`a₀ ×_T b₀ + a₁ ×_T b₁ + a₂ ×_T b₂` to polynomial 15 (`dotAt_ok`,
`dotAt_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (h : keepB bs ws p l = true) (hs : ∀ w ∈ ws', w ∈ ws) : keepB bs ws' p l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw => h.2 w (hs w hw)⟩

/-! ## `PRF₂(σ, N)` -/

theorem shake31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The bytes absorbed: `σ ‖ N`. -/
theorem prf_pieces {s : State} {N : Nat} (hN : bytesAt s.mem (pa s (sc oNB)) 1 = [BitVec.ofNat 8 N]) :
    pieces s [(sigP, 32), (sc oNB, 1)] = bytesAt s.mem (pa s sigP) 32 ++ [BitVec.ofNat 8 N] := by
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hN]

/-! ## Sequences, for constant time -/

/-- Two pieces of code in sequence, from two runs in a layout that satisfy
`I` (what the first piece needs), each piece leaving the layout. -/
theorem RelCT.seqL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c₁ c₂ : Prog isa}
    {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay rbs wbs x → I x → WP isa c₁ x fun x' => (∃ W, PostB x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => LRel rbs wbs x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, PostB x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.1 h.2.1, w₁ y h.1.2.1 h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩) h₂

/-! ## Sums of products -/

/-- The polynomials a sum of products writes. -/
abbrev W3 : List (Ptr × Nat) := [(pS 15, 1024), (pS 16, 1024), (sc oSS, 1024)]

def dotChk (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) : Bool :=
  (List.range 3).all (fun k => keepB bs W3 (f k) 1024 && keepB bs W3 (g k) 1024 && decide (NA (f k)) &&
      decide (NA (g k))) &&
    mulChk bs wbs (pS 15) (f 0) (g 0) && mulChk bs wbs (pS 16) (f 1) (g 1) && mulChk bs wbs (pS 16) (f 2) (g 2) &&
    accChk bs wbs (pS 15) (pS 16) && keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024

theorem dotChk_spec {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} (h : dotChk bs wbs f g = true) :
    (∀ k < 3, keepB bs W3 (f k) 1024 = true ∧ keepB bs W3 (g k) 1024 = true ∧ NA (f k) ∧ NA (g k)) ∧
    mulChk bs wbs (pS 15) (f 0) (g 0) = true ∧ mulChk bs wbs (pS 16) (f 1) (g 1) = true ∧
    mulChk bs wbs (pS 16) (f 2) (g 2) = true ∧ accChk bs wbs (pS 15) (pS 16) = true ∧
    keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024 = true := by
  simp only [dotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun k hk => by have := h0 k hk; exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩, h1, h2, h3, h4, h5⟩

/-- The sum of products `a₀ b₀ + a₁ b₁ + a₂ b₂`, accumulated left to right. -/
theorem dotAt_ok {A : Arith} (hA : ArithOk A) {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {f g : Nat → Ptr} (hc : dotChk (rbs ++ wbs) wbs f g = true)
    {a b : Nat → Poly} (ha : ∀ k < 3, PolyIs s.mem (pa s (f k)) (a k)) (hb : ∀ k < 3, PolyIs s.mem (pa s (g k)) (b k)) :
    WP isa (dotAt A f g) s fun s' =>
      PPost s s' ([(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)] ++
        [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]) ∧
      PolyIs s'.mem (pa s (pS 15)) (dot3 a b) := by
  obtain ⟨hk, hm0, hm1, hm2, hac, hk15⟩ := dotChk_spec hc
  have W3s : ∀ ws : List (Ptr × Nat), (∀ w ∈ ws, w ∈ W3) → ∀ k < 3,
      keepB (rbs ++ wbs) ws (f k) 1024 = true ∧ keepB (rbs ++ wbs) ws (g k) 1024 = true :=
    fun ws hws k hk3 => ⟨keepB_sub (hk k hk3).1 hws, keepB_sub (hk k hk3).2.1 hws⟩
  have s1 : ∀ w ∈ [(pS 15, 1024), (sc oSS, 1024)], w ∈ W3 := by decide
  have s2 : ∀ w ∈ [(pS 16, 1024), (sc oSS, 1024)], w ∈ W3 := by decide
  have s3 : ∀ w ∈ [(pS 15, 1024)], w ∈ W3 := by decide
  unfold dotAt
  -- f 0 × g 0
  refine WP.seq (WP.mono (mulAt_okL hA L (hk 0 (by decide)).2.2.1 (hk 0 (by decide)).2.2.2 hm0 (ha 0 (by decide)).1
    (hb 0 (by decide)).1) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  have ha₁ : ∀ k < 3, PolyIs s₁.mem (pa s₁ (f k)) (a k) := fun k hk3 => L.keepPoly hP₁.b (W3s _ s1 k hk3).1 (ha k hk3)
  have hb₁ : ∀ k < 3, PolyIs s₁.mem (pa s₁ (g k)) (b k) := fun k hk3 => L.keepPoly hP₁.b (W3s _ s1 k hk3).2 (hb k hk3)
  rw [(ha 0 (by decide)).2, (hb 0 (by decide)).2, ← hP₁.pa rbx_cs] at hp₁
  -- f 1 × g 1
  refine WP.seq (WP.mono (mulAt_okL hA L₁ (hk 1 (by decide)).2.2.1 (hk 1 (by decide)).2.2.2 hm1 (ha₁ 1 (by decide)).1
    (hb₁ 1 (by decide)).1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b hcs
  have ha₂ : ∀ k < 3, PolyIs s₂.mem (pa s₂ (f k)) (a k) := fun k hk3 => L₁.keepPoly hP₂.b (W3s _ s2 k hk3).1 (ha₁ k hk3)
  have hb₂ : ∀ k < 3, PolyIs s₂.mem (pa s₂ (g k)) (b k) := fun k hk3 => L₁.keepPoly hP₂.b (W3s _ s2 k hk3).2 (hb₁ k hk3)
  rw [(ha₁ 1 (by decide)).2, (hb₁ 1 (by decide)).2, ← hP₂.pa rbx_cs] at hp₂
  have hq₂ := L₁.keepPoly hP₂.b hk15 hp₁
  -- sum
  refine WP.seq (WP.mono (addAt_ok L₂ rbx_na hac hq₂.1 hp₂.1) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b hcs
  have ha₃ : ∀ k < 3, PolyIs s₃.mem (pa s₃ (f k)) (a k) := fun k hk3 => L₂.keepPoly hP₃.b (W3s _ s3 k hk3).1 (ha₂ k hk3)
  have hb₃ : ∀ k < 3, PolyIs s₃.mem (pa s₃ (g k)) (b k) := fun k hk3 => L₂.keepPoly hP₃.b (W3s _ s3 k hk3).2 (hb₂ k hk3)
  rw [hq₂.2, hp₂.2, ← hP₃.pa rbx_cs] at hp₃
  -- f 2 × g 2
  refine WP.seq (WP.mono (mulAt_okL hA L₃ (hk 2 (by decide)).2.2.1 (hk 2 (by decide)).2.2.2 hm2 (ha₃ 2 (by decide)).1
    (hb₃ 2 (by decide)).1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b hcs
  rw [(ha₃ 2 (by decide)).2, (hb₃ 2 (by decide)).2, ← hP₄.pa rbx_cs] at hp₄
  have hq₄ := L₃.keepPoly hP₄.b hk15 hp₃
  refine WP.mono (addAt_ok L₄ rbx_na hac hq₄.1 hp₄.1) fun s₅ ⟨hP₅, hp₅⟩ => ⟨PPost.app (PPost.app (PPost.app
    (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅ (by decide), ?_⟩
  rw [hq₄.2, hp₄.2, hP₄.pa rbx_cs, hP₃.pa rbx_cs, hP₂.pa rbx_cs, hP₁.pa rbx_cs] at hp₅
  exact hp₅

/-- The inputs of a sum of products, reduced. -/
abbrev DotIn (f g : Nat → Ptr) (s : State) : Prop :=
  ∀ k < 3, Reduced s.mem (pa s (f k)) ∧ Reduced s.mem (pa s (g k))

theorem dotAt_tr {A : Arith} (hA : ArithOk A) {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {f g : Nat → Ptr}
    (hc : dotChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ DotIn f g x ∧ DotIn f g y) (dotAt A f g) fun _ _ => True := by
  obtain ⟨hk, hm0, hm1, hm2, hac, hk15⟩ := dotChk_spec hc
  have W3s : ∀ ws : List (Ptr × Nat), (∀ w ∈ ws, w ∈ W3) → ∀ k < 3,
      keepB (rbs ++ wbs) ws (f k) 1024 = true ∧ keepB (rbs ++ wbs) ws (g k) 1024 = true :=
    fun ws hws k hk3 => ⟨keepB_sub (hk k hk3).1 hws, keepB_sub (hk k hk3).2.1 hws⟩
  have s1 : ∀ w ∈ [(pS 15, 1024), (sc oSS, 1024)], w ∈ W3 := by decide
  have s2 : ∀ w ∈ [(pS 16, 1024), (sc oSS, 1024)], w ∈ W3 := by decide
  have s3 : ∀ w ∈ [(pS 15, 1024)], w ∈ W3 := by decide
  have keepIn : ∀ {x x' : State} {ws : List (Ptr × Nat)}, Lay rbs wbs x → PPostB x x' ws → (∀ w ∈ ws, w ∈ W3) →
      DotIn f g x → DotIn f g x' := fun Lx hP hws hi k hk3 =>
    ⟨Lx.keepRed hP (W3s _ hws k hk3).1 (hi k hk3).1, Lx.keepRed hP (W3s _ hws k hk3).2 (hi k hk3).2⟩
  unfold dotAt
  refine RelCT.seqL (J := fun x => DotIn f g x ∧ Reduced x.mem (pa x (pS 15))) hcs
    (RelCT.mono (mulAt_trL hA (hk 0 (by decide)).2.2.1 (hk 0 (by decide)).2.2.2 hm0)
      (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1 0 (by decide), i2 0 (by decide)⟩) fun _ _ _ => trivial)
    (fun x Lx hi => WP.mono (mulAt_okL hA Lx (hk 0 (by decide)).2.2.1 (hk 0 (by decide)).2.2.2 hm0 (hi 0 (by decide)).1
      (hi 0 (by decide)).2) fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩, keepIn Lx hP.b s1 hi, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
  refine RelCT.seqL (J := fun x => DotIn f g x ∧ Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) hcs
    (RelCT.mono (mulAt_trL hA (hk 1 (by decide)).2.2.1 (hk 1 (by decide)).2.2.2 hm1)
      (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1.1 1 (by decide), i2.1 1 (by decide)⟩) fun _ _ _ => trivial)
    (fun x Lx hi => WP.mono (mulAt_okL hA Lx (hk 1 (by decide)).2.2.1 (hk 1 (by decide)).2.2.2 hm1
      (hi.1 1 (by decide)).1 (hi.1 1 (by decide)).2) fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩, keepIn Lx hP.b s2 hi.1,
        Lx.keepRed hP.b hk15 hi.2, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
  refine RelCT.seqL (J := fun x => DotIn f g x ∧ Reduced x.mem (pa x (pS 15))) hcs
    (RelCT.mono (addAt_tr rbx_na hac) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1.2, i2.2⟩) fun _ _ _ => trivial)
    (fun x Lx hi => WP.mono (addAt_ok Lx rbx_na hac hi.2.1 hi.2.2) fun x' ⟨hP, hp⟩ =>
      ⟨⟨_, hP.b⟩, keepIn Lx hP.b s3 hi.1, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
  refine RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) hcs
    (RelCT.mono (mulAt_trL hA (hk 2 (by decide)).2.2.1 (hk 2 (by decide)).2.2.2 hm2)
      (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1.1 2 (by decide), i2.1 2 (by decide)⟩) fun _ _ _ => trivial)
    (fun x Lx hi => WP.mono (mulAt_okL hA Lx (hk 2 (by decide)).2.2.1 (hk 2 (by decide)).2.2.2 hm2
      (hi.1 2 (by decide)).1 (hi.1 2 (by decide)).2) fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩,
        Lx.keepRed hP.b hk15 hi.2, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
  exact RelCT.mono (addAt_tr rbx_na hac) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1, i2⟩) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
