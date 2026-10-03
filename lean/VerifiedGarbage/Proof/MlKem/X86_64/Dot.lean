import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Impl.MlKem.X86_64.Kem

/-!
# ML-KEM on x86-64: sums of products

`a₀ ×_T b₀ + ⋯ + a_{n-1} ×_T b_{n-1}` to polynomial 15 (`dotN`), proven for
every `n` by induction (`dotN_ok`, `dotN_tr`): `KPke.dotK`, accumulated left
to right.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The polynomials a sum of products writes. -/
abbrev W3 : List (Ptr × Nat) := [(pS 15, 1024), (pS 16, 1024), (sc oSS, 1024)]

/-- What a sum of `n` products writes. -/
def dotW : Nat → List (Ptr × Nat)
  | 0 => []
  | 1 => [(pS 15, 1024), (sc oSS, 1024)]
  | n + 2 => dotW (n + 1) ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]

theorem dotW_W3 : ∀ n, ∀ w ∈ dotW n, w ∈ W3
  | 0 => fun _ h => absurd h List.not_mem_nil
  | 1 => by decide
  | n + 2 => fun w hw => by
    simp only [dotW, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · exact dotW_W3 (n + 1) w hw
    · revert w; decide
    · revert w; decide

/-- The checks of a sum of `n` products of `f k` and `g k`. -/
def dotChk (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) (n : Nat) : Bool :=
  (List.range n).all (fun k => keepB bs W3 (f k) 1024 && keepB bs W3 (g k) 1024 && decide (NA (f k)) &&
      decide (NA (g k))) &&
    mulChk bs wbs (pS 15) (f 0) (g 0) && (List.range n).all (fun k => mulChk bs wbs (pS 16) (f k) (g k)) &&
    accChk bs wbs (pS 15) (pS 16) && keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024

/-- `dotChk`, as facts. -/
structure DotChks (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) (n : Nat) : Prop where
  k : ∀ k < n, keepB bs W3 (f k) 1024 = true ∧ keepB bs W3 (g k) 1024 = true ∧ NA (f k) ∧ NA (g k)
  m0 : mulChk bs wbs (pS 15) (f 0) (g 0) = true
  m : ∀ k < n, mulChk bs wbs (pS 16) (f k) (g k) = true
  acc : accChk bs wbs (pS 15) (pS 16) = true
  k15 : keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024 = true

theorem dotChk_spec {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} {n : Nat} (h : dotChk bs wbs f g n = true) :
    DotChks bs wbs f g n := by
  simp only [dotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun k hk => by have := h0 k hk; exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩, h1, h2, h3, h4⟩

theorem DotChks.mono {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} {n n' : Nat} (h : DotChks bs wbs f g n)
    (hn : n' ≤ n) : DotChks bs wbs f g n' :=
  ⟨fun k hk => h.k k (by omega), h.m0, fun k hk => h.m k (by omega), h.acc, h.k15⟩

/-- The sum of products `a₀ b₀ + ⋯ + a_{n-1} b_{n-1}`, accumulated left to right. -/
theorem dotN_ok {A : Arith} (hA : ArithOk A) {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {f g : Nat → Ptr} {a b : Nat → Poly} :
    ∀ {n : Nat}, 0 < n → DotChks (rbs ++ wbs) wbs f g n → ∀ {s : State}, Lay rbs wbs s →
      (∀ k < n, PolyIs s.mem (pa s (f k)) (a k)) → (∀ k < n, PolyIs s.mem (pa s (g k)) (b k)) →
      WP isa (dotN A f g n) s fun s' => PPost s s' (dotW n) ∧ PolyIs s'.mem (pa s (pS 15)) (KPke.dotK a b n)
  | 0, h, _, _, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, hc, s, L, ha, hb => by
    refine WP.mono (mulAt_okL hA L (hc.k 0 (by decide)).2.2.1 (hc.k 0 (by decide)).2.2.2 hc.m0 (ha 0 (by decide)).1
      (hb 0 (by decide)).1) fun s₁ ⟨hP₁, hp₁⟩ => ⟨hP₁, ?_⟩
    rw [(ha 0 (by decide)).2, (hb 0 (by decide)).2] at hp₁
    exact hp₁
  | n + 2, _, hc, s, L, ha, hb => by
    have W3s : ∀ {ws : List (Ptr × Nat)}, (∀ w ∈ ws, w ∈ W3) → ∀ k < n + 2,
        keepB (rbs ++ wbs) ws (f k) 1024 = true ∧ keepB (rbs ++ wbs) ws (g k) 1024 = true :=
      fun hws k hk => ⟨keepB_sub (hc.k k hk).1 hws, keepB_sub (hc.k k hk).2.1 hws⟩
    refine WP.seq (WP.mono (dotN_ok hA hcs (n := n + 1) (by omega) (hc.mono (by omega)) L
      (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega))) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
    have L₁ := L.post hP₁.b hcs
    have ha₁ := L.keepPoly hP₁.b (W3s (dotW_W3 _) (n + 1) (by omega)).1 (ha (n + 1) (by omega))
    have hb₁ := L.keepPoly hP₁.b (W3s (dotW_W3 _) (n + 1) (by omega)).2 (hb (n + 1) (by omega))
    rw [← hP₁.pa rbx_cs] at hp₁
    refine WP.seq (WP.mono (mulAt_okL hA L₁ (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
      (hc.m (n + 1) (by omega)) ha₁.1 hb₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
    have L₂ := L₁.post hP₂.b hcs
    rw [ha₁.2, hb₁.2, ← hP₂.pa rbx_cs] at hp₂
    have hq₂ := L₁.keepPoly hP₂.b hc.k15 hp₁
    refine WP.mono (addAt_ok L₂ rbx_na hc.acc hq₂.1 hp₂.1) fun s₃ ⟨hP₃, hp₃⟩ =>
      ⟨PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide), ?_⟩
    rw [hq₂.2, hp₂.2, hP₂.pa rbx_cs, hP₁.pa rbx_cs] at hp₃
    exact hp₃

/-- The inputs of a sum of `n` products, reduced. -/
abbrev DotIn (f g : Nat → Ptr) (n : Nat) (s : State) : Prop :=
  ∀ k < n, Reduced s.mem (pa s (f k)) ∧ Reduced s.mem (pa s (g k))

theorem dotN_tr {A : Arith} (hA : ArithOk A) {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {f g : Nat → Ptr} : ∀ {n : Nat}, 0 < n → DotChks (rbs ++ wbs) wbs f g n →
      RelCT isa (fun x y => LRel rbs wbs x y ∧ DotIn f g n x ∧ DotIn f g n y) (dotN A f g n) fun _ _ => True
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, hc => RelCT.mono (mulAt_trL hA (hc.k 0 (by decide)).2.2.1 (hc.k 0 (by decide)).2.2.2 hc.m0)
      (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1 0 (by decide), i2 0 (by decide)⟩) fun _ _ _ => trivial
  | n + 2, _, hc => by
    have keep : ∀ {x x' : State} {ws : List (Ptr × Nat)}, Lay rbs wbs x → PPostB x x' ws → (∀ w ∈ ws, w ∈ W3) →
        DotIn f g (n + 2) x → DotIn f g (n + 2) x' := fun Lx hP hws hi k hk =>
      ⟨Lx.keepRed hP (keepB_sub (hc.k k hk).1 hws) (hi k hk).1, Lx.keepRed hP (keepB_sub (hc.k k hk).2.1 hws) (hi k hk).2⟩
    refine RelCT.seqL (J := fun x => DotIn f g (n + 2) x ∧ Reduced x.mem (pa x (pS 15))) hcs
      (RelCT.mono (dotN_tr hA hcs (n := n + 1) (by omega) (hc.mono (by omega)))
        (fun _ _ ⟨e, i1, i2⟩ => ⟨e, fun k hk => i1 k (by omega), fun k hk => i2 k (by omega)⟩) fun _ _ _ => trivial)
      (fun x Lx hi => WP.mono (dotN_ok hA hcs (a := fun k => polyAt x.mem (pa x (f k)))
        (b := fun k => polyAt x.mem (pa x (g k))) (n := n + 1) (by omega) (hc.mono (by omega)) Lx
        (fun k hk => ⟨(hi k (by omega)).1, rfl⟩) (fun k hk => ⟨(hi k (by omega)).2, rfl⟩))
        fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩, keep Lx hP.b (dotW_W3 _) hi, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
    refine RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) hcs
      (RelCT.mono (mulAt_trL hA (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
          (hc.m (n + 1) (by omega)))
        (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1.1 (n + 1) (by omega), i2.1 (n + 1) (by omega)⟩) fun _ _ _ => trivial)
      (fun x Lx hi => WP.mono (mulAt_okL hA Lx (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
        (hc.m (n + 1) (by omega)) (hi.1 (n + 1) (by omega)).1 (hi.1 (n + 1) (by omega)).2) fun x' ⟨hP, hp⟩ =>
          ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hc.k15 hi.2, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
    exact RelCT.mono (addAt_tr rbx_na hc.acc) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1, i2⟩) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
