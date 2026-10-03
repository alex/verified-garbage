import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpack

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the coefficients of a polynomial

Once the bound `y[ω + i]` of polynomial `i` has passed its checks, the code
sets the coefficients `y[index]` up to it (`coefs_piece`), following `huStep`
from the spec's state `cur s₀ i` before the polynomial: after `t` of them the
spec's state is `G s₀ i t`, and `eax` its index (or 256 once a check fails,
which ends the loop).
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state before polynomial `i`, if no check failed. -/
def cur (s₀ : State) (i : Nat) : Array (Vector Bool n) × Nat := (PS s₀ i).getD (#[], 0)

/-- Its index. -/
abbrev fst (s₀ : State) (i : Nat) : Nat := (cur s₀ i).2

/-- ... and after `t` of the coefficients of polynomial `i`. -/
def G (s₀ : State) (i t : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huStep (Y s₀) i (fst s₀ i)) (List.range t) (cur s₀ i)

theorem Pub.ecur {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : cur s₀ i = cur s₀' i := by
  unfold cur; rw [h.ePS]

theorem Pub.eG {s₀ s₀' : State} (h : Pub s₀ s₀') (i t : Nat) : G s₀ i t = G s₀' i t := by
  show optFold (huStep (Y s₀) i (cur s₀ i).2) (List.range t) (cur s₀ i) =
    optFold (huStep (Y s₀') i (cur s₀' i).2) (List.range t) (cur s₀' i)
  rw [h.ecur, h.y]

theorem G_succ (s₀ : State) (i t : Nat) :
    G s₀ i (t + 1) = (G s₀ i t).bind fun st => huStep (Y s₀) i (fst s₀ i) st t :=
  optFold_range_succ _ _ _

theorem G_idx (s₀ : State) (i : Nat) : ∀ {t : Nat} {st : Array (Vector Bool n) × Nat}, G s₀ i t = some st →
    st.2 = fst s₀ i + t
  | 0, st, h => by simp only [G, List.range_zero, optFold, Option.some.injEq] at h; subst h; rfl
  | t + 1, st, h => by
    rw [G_succ] at h
    cases e : G s₀ i t with
    | none => rw [e] at h; cases h
    | some st' =>
      rw [e, Option.bind_some] at h
      rw [huStep_idx h, G_idx s₀ i e]; omega

theorem idxOf_G {s₀ : State} {i t : Nat} (h : idxOf (G s₀ i t) < 256) : ∃ st, G s₀ i t = some st ∧
    idxOf (G s₀ i t) = fst s₀ i + t := by
  cases e : G s₀ i t with
  | none => rw [e] at h; exact absurd h (by decide)
  | some st => exact ⟨st, rfl, G_idx s₀ i e⟩

theorem PS_succ (s₀ : State) (i : Nat) :
    PS s₀ (i + 1) = (PS s₀ i).bind fun st => huPoly (ω s₀) (Y s₀) st i :=
  optFold_range_succ _ _ _

theorem bnd_lt (s₀ : State) (i : Nat) : bnd s₀ i < 256 := yb_lt _ _

/-- A bound less than the index fails. -/
theorem PS_fail₁ {s₀ : State} {i : Nat} (h : bnd s₀ i < idxOf (PS s₀ i)) : PS s₀ (i + 1) = none := by
  rw [PS_succ]
  cases e : PS s₀ i with
  | none => rfl
  | some st =>
    rw [e] at h
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inl h) _ _

/-- A bound greater than `ω` fails. -/
theorem PS_fail₂ {s₀ : State} {i : Nat} (h : bnd s₀ i > ω s₀) : PS s₀ (i + 1) = none := by
  rw [PS_succ]
  cases e : PS s₀ i with
  | none => rfl
  | some st =>
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inr h) _ _

/-- Otherwise the coefficients follow. -/
theorem PS_ok {s₀ : State} {i : Nat} (h₁ : ¬ bnd s₀ i < idxOf (PS s₀ i)) (h₂ : ¬ bnd s₀ i > ω s₀) :
    PS s₀ i = some (cur s₀ i) ∧ fst s₀ i ≤ bnd s₀ i ∧ PS s₀ (i + 1) = G s₀ i (bnd s₀ i - fst s₀ i) := by
  cases e : PS s₀ i with
  | none => rw [e] at h₁; exact absurd (bnd_lt s₀ i) h₁
  | some st =>
    have ec : cur s₀ i = st := by unfold cur; rw [e]; rfl
    have ef : fst s₀ i = st.2 := by show (cur s₀ i).2 = _; rw [ec]
    have eb : bnd s₀ i = ((Y s₀).getD (ω s₀ + i) 0).toNat := rfl
    rw [e] at h₁
    simp only [idxOf] at h₁
    refine ⟨by rw [ec], by omega, ?_⟩
    rw [PS_succ, e, Option.bind_some, huPoly, ite_neg' (by omega), G]
    show _ = optFold (huStep (Y s₀) i (cur s₀ i).2) (List.range (bnd s₀ i - (cur s₀ i).2)) (cur s₀ i)
    rw [ec]

/-! ## The state within a polynomial -/

/-- Within polynomial `i`, whose bound passed its checks, with the spec's
state `o`. -/
structure IM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends Ptr s₀ i s where
  ebx : s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)
  eax : s.gpr .eax = BitVec.ofNat 32 (idxOf o)
  sr : SR s₀ o s.mem
  hi : i < K s₀
  some : PS s₀ i = some (cur s₀ i)
  fb : fst s₀ i ≤ bnd s₀ i
  bw : bnd s₀ i ≤ ω s₀

/-- `IM`, after a block that writes only `edx`, `ebp` and the flags. -/
theorem IM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : IM s₀ i o s)
    (k : Keep [.edx, .ebp] s s') (hm : s'.mem = s.mem) : IM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp) hm,
    by rw [k.gpr (by decide), h.ebx], by rw [k.gpr (by decide), h.eax], by rw [hm]; exact h.sr, h.hi, h.some,
    h.fb, h.bw⟩

theorem idx_lt_yL {s₀ : State} (hp : Pre s₀) {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} {s : State}
    (h : IM s₀ i o s) {t : Nat} (ht : t < bnd s₀ i) : t < yL s₀ := by
  have := hp.facts; have := h.bw; omega

/-- The `SR` of `G`, from that of the state before. -/
theorem SR_G {s₀ : State} {i t : Nat} {m : Mem} (hfb : fst s₀ i + t ≤ bnd s₀ i) (hbw : bnd s₀ i ≤ ω s₀)
    (h : ∀ st, G s₀ i t = some st → HArr m (wA s₀) (K s₀) st.1) : SR s₀ (G s₀ i t) m :=
  fun st e => ⟨by rw [G_idx s₀ i e]; omega, h st e⟩

/-! ## Setting a coefficient -/

/-- `ebp ← 4b + ecx`, the word of coefficient `b` of polynomial `i`. -/
theorem setAddr {x : BitVec 32} {i b : Nat} (hx : x.toNat + 1024 * i + 4 * b + 4 ≤ 2 ^ 32) :
    addr (BitVec.ofNat 32 b + BitVec.ofNat 32 b + (BitVec.ofNat 32 b + BitVec.ofNat 32 b) +
      (x + BitVec.ofNat 32 (1024 * i))) 0 = x.setWidth 64 + BitVec.ofNat 64 (4 * (256 * i + b)) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm, BitVec.add_assoc, ofNat_add_ofNat,
    addr_add (by omega)]
  congr 2; omega

theorem set_wp {s₀ s : State} (hp : Pre s₀) {i b : Nat} (h : Ptr s₀ i s) (hi : i < K s₀) (hb : b < 256)
    (hebp : s.gpr .ebp = BitVec.ofNat 32 b) :
    WP isa (.block hbuSet) s fun s' => (s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) ∧ Keep [.ebp, .eax] s s' := by
  have hf := hp.facts
  have hw := hp.w_fit
  have ht : 256 * i + b < 256 * K s₀ := by omega
  have ea : addr (s.gpr .ebp + s.gpr .ebp + (s.gpr .ebp + s.gpr .ebp) + s.gpr .ecx) 0 =
      coeffAddr (wA s₀) (256 * i + b) := by
    rw [hebp, h.ecx]; exact setAddr (by omega)
  have hin := h.inH hp ht
  refine WP.keep _ ?_ (by decide)
  hrun [hbuSet, ea, hin, h.esi]

/-- After setting coefficient `b` of polynomial `i`. -/
theorem sr_set {s₀ : State} (hp : Pre s₀) {i b : Nat} (hi : i < K s₀) (hb : b < 256) {m : Mem}
    {hA : Array (Vector Bool n)} (hh : HArr m (wA s₀) (K s₀) hA) :
    HArr (m.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) (wA s₀) (K s₀) (huSet i b hA) := by
  have := hp.facts
  exact harr_set (by omega) hh hi hb

/-- The frame of the write. -/
theorem ptr_set {s₀ s s' : State} (hp : Pre s₀) {i b : Nat} (h : Ptr s₀ i s) (hi : i < K s₀) (hb : b < 256)
    (k : Keep [.ebp, .eax] s s') (hm : s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) :
    Ptr s₀ i s' := by
  have hf := hp.facts
  have ht : 256 * i + b < 256 * K s₀ := by omega
  have g : ∀ r, r ≠ .eax → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a c =>
    k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun hh => hh.elim c a)
  exact ⟨h.toBase.keep k (by decide) (by rw [hm]; exact frame_coeff hp ht _),
    by rw [g _ (by decide) (by decide), h.edi], by rw [g _ (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide), h.ecx],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega)) (by decide), h.cnt],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega)) (by decide), h.ptr]⟩

theorem idxOf_le {s₀ : State} (hp : Pre s₀) {o : Option (Array (Vector Bool n) × Nat)} {m : Mem}
    (h : SR s₀ o m) : idxOf o ≤ 256 := by
  cases o with
  | none => exact Nat.le_refl _
  | some st => have := (h st rfl).1; have := hp.facts; show st.2 ≤ 256; omega

theorem G_next {s₀ : State} {i t : Nat} {st : Array (Vector Bool n) × Nat} (e : G s₀ i t = some st) :
    G s₀ i (t + 1) = if st.2 > fst s₀ i ∧ yb s₀ (st.2 - 1) ≥ yb s₀ st.2 then none
      else some (huSet i (yb s₀ st.2) st.1, st.2 + 1) := by
  rw [G_succ, e]; rfl

theorem G_one (s₀ : State) (i : Nat) :
    G s₀ i 1 = some (huSet i (yb s₀ (fst s₀ i)) (cur s₀ i).1, fst s₀ i + 1) := by
  rw [G_next (t := 0) rfl, ite_neg' (fun h => Nat.lt_irrefl _ h.1)]

/-- `cmp eax, ebx`: whether the index is below the bound. -/
theorem cmp_piece (i : Nat) (o : State → Option (Array (Vector Bool n) × Nat)) (X : State → Prop) :
    Piece Pre Pub (fun s₀ s => IM s₀ i (o s₀) s ∧ X s₀)
      (fun s₀ s => (IM s₀ i (o s₀) s ∧ X s₀) ∧ isa.eval .b s = some (decide (idxOf (o s₀) < bnd s₀ i)))
      (.block [.alu .cmp .eax (.reg .ebx)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .eax).toNat < (s.gpr .ebx).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
        s'.mem = s.mem := by hrun
  have hl := idxOf_le hp h.sr
  have hb' := bnd_lt s₀ i
  refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k⟩ =>
    ⟨⟨h.keep ⟨fun r _ => (k.drop ea).gpr (by simp), k.2⟩ m, hx⟩, ?_⟩
  show s'.cf = _
  rw [c, h.eax, h.ebx, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

/-- The first coefficient: `ebp = y[index]`. -/
theorem first_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i)
    (fun s₀ s => (IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i)))
    (.block hbuFirst) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp ⟨h, hl⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by taint_decide)
  · have hy := idx_lt_yL hp h hl
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i) := by
      rw [h.edi, h.eax]; exact yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block hbuFirst) s fun s' => s'.gpr .ebp = BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i) 0) ∧
        s'.mem = s.mem := by
      hrun [hbuFirst, ea, hin, hv]
    exact (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ => ⟨⟨h.keep k m, hl⟩, by rw [e, byte32]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.edi, h'.edi, hq.a0]
    · rw [h.eax, h'.eax, hq.eG]

/-- The first coefficient set, and whether the index is below the bound. -/
theorem set1_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i)))
    (fun s₀ s => IM s₀ i (G s₀ i 1) s ∧ isa.eval .b s = some (decide (fst s₀ i + 1 < bnd s₀ i)))
    (.block (hbuSet ++ ([.alu .cmp .eax (.reg .ebx)] : List Instr))) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨h, hl⟩, he⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨h, _⟩, he⟩ ⟨⟨h', _⟩, he'⟩ r hr => ?_) (by taint_decide)
  · have hb' := bnd_lt s₀ i
    have hbw := h.bw
    have hf := hp.facts
    refine WP.block_append ((set_wp hp h.toPtr h.hi (yb_lt s₀ _) he).mono fun s₁ ⟨⟨e1, m1⟩, k1⟩ => ?_)
    have hc : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s₁ fun s' =>
        s'.cf = some (decide ((s₁.gpr .eax).toNat < (s₁.gpr .ebx).toNat)) ∧ s'.gpr .eax = s₁.gpr .eax ∧
          s'.mem = s₁.mem := by hrun
    refine (WP.keep [.eax] hc (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨(ptr_set hp h.toPtr h.hi (yb_lt s₀ _) k1 m1).keep k (fun r hr => by simp at hr) m, ?_, ?_, ?_, h.hi,
      h.some, h.fb, h.bw⟩, ?_⟩
    · rw [k.gpr (by simp), k1.gpr (by decide), h.ebx]
    · rw [k.gpr (by simp), e1, h.eax, G_one]; simp only [idxOf]; rw [ofNat_add_one]; rfl
    · rw [m, m1]
      refine SR_G (t := 1) (by omega) hbw fun st e => ?_
      rw [G_one, Option.some.injEq] at e
      subst e
      obtain ⟨-, hh⟩ := h.sr (cur s₀ i) (by rw [G]; rfl)
      exact sr_set hp h.hi (yb_lt s₀ _) hh
    · show s'.cf = _
      rw [c, e1, h.eax, k1.gpr (by decide), h.ebx]
      simp only [G, List.range_zero, optFold, idxOf]
      have : fst s₀ i = (cur s₀ i).2 := rfl
      rw [ofNat_add_one, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (yb s₀ (cur s₀ i).2) = BitVec.ofNat 32 (yb s₀' (cur s₀' i).2)
      rw [hq.ecur, hq.eyb]
    · rw [h.ecx, h'.ecx, hq.a3]

/-! ## The coefficients after the first -/

/-- Before iteration `k` of the loop: `k + 1` coefficients set, and the
index below the bound. -/
def NI (i k : Nat) (s₀ s : State) : Prop :=
  IM s₀ i (G s₀ i (k + 1)) s ∧ idxOf (G s₀ i (k + 1)) = fst s₀ i + k + 1 ∧ fst s₀ i + k + 1 < bnd s₀ i

/-- `ebp = y[index]`, and whether `y[index - 1] < y[index]`. -/
theorem loads_piece (i k : Nat) : Piece Pre Pub (NI i k)
    (fun s₀ s => (NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1))))
    (.block hbuLoads) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · obtain ⟨hI, hx, hl⟩ := h
    have hy := idx_lt_yL hp hI hl
    have hax : s.gpr .eax = BitVec.ofNat 32 (fst s₀ i + k + 1) := by rw [hI.eax, hx]
    have ea1 : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i + k + 1) := by
      rw [hI.edi, hax]; exact yAddr hp hy
    have ea2 : addr (s.gpr .edi + s.gpr .eax - 1) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i + k) := by
      rw [hI.edi, hax, add_sub_one' _ (by omega)]; exact yAddr hp (by omega)
    have i1 := hI.inY hp hy
    have i2 := hI.inY hp (t := fst s₀ i + k) (by omega)
    have v1 := hI.ybyte hp hy
    have v2 := hI.ybyte hp (t := fst s₀ i + k) (by omega)
    have hb : WP isa (.block hbuLoads) s fun s' =>
        s'.gpr .ebp = BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k + 1) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k) 0)).toNat <
          (BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k + 1) 0)).toNat)) ∧ s'.mem = s.mem := by
      hrun [hbuLoads, ea1, ea2, i1, i2, v1, v2]
    refine (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k'⟩ =>
      ⟨⟨⟨hI.keep k' m, hx, hl⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, toNat_setWidth32_8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.1.eax, h'.1.eax, hq.eG]

theorem G_some {s₀ : State} {i k : Nat} (h : idxOf (G s₀ i (k + 1)) = fst s₀ i + k + 1) (hl : fst s₀ i + k + 1 < 256) :
    ∃ st, G s₀ i (k + 1) = some st ∧ st.2 = fst s₀ i + k + 1 := by
  obtain ⟨st, e, -⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 1) (by omega)
  exact ⟨st, e, by rw [e] at h; exact h⟩

/-- A coefficient greater than the previous one: set it. -/
theorem set2_piece (i k : Nat) : Piece Pre Pub
    (fun s₀ s => ((NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)))) ∧
      decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)) = true)
    (fun s₀ s => IM s₀ i (G s₀ i (k + 2)) s ∧ fst s₀ i + k + 1 < bnd s₀ i) (.block hbuSet) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨hn, he⟩, _⟩, _⟩ ⟨⟨⟨hn', he'⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have hlt := of_decide_eq_true hb
    have hb' := bnd_lt s₀ i
    obtain ⟨st, e, est⟩ := G_some hx (by omega)
    have hG : G s₀ i (k + 2) = some (huSet i (yb s₀ (fst s₀ i + k + 1)) st.1, fst s₀ i + k + 1 + 1) := by
      rw [G_next e, est, ite_neg' (fun h => by
        rw [show fst s₀ i + k + 1 - 1 = fst s₀ i + k by omega] at h; omega)]
    refine (set_wp hp hI.toPtr hI.hi (yb_lt s₀ _) he).mono fun s' ⟨⟨e1, m1⟩, k1⟩ =>
      ⟨⟨ptr_set hp hI.toPtr hI.hi (yb_lt s₀ _) k1 m1, by rw [k1.gpr (by decide), hI.ebx], ?_, ?_, hI.hi, hI.some,
        hI.fb, hI.bw⟩, hl⟩
    · rw [e1, hI.eax, hx, hG]; simp only [idxOf]; rw [ofNat_add_one]
    · rw [m1]
      refine SR_G (t := k + 2) (by omega) hI.bw fun st' e' => ?_
      rw [hG, Option.some.injEq] at e'
      subst e'
      exact sr_set hp hI.hi (yb_lt s₀ _) (hI.sr st e).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (yb s₀ ((cur s₀ i).2 + k + 1)) = BitVec.ofNat 32 (yb s₀' ((cur s₀' i).2 + k + 1))
      rw [hq.ecur, hq.eyb]
    · rw [hn.1.ecx, hn'.1.ecx, hq.a3]

/-- A coefficient not greater than the previous one: fail. -/
theorem fail2_piece (i k : Nat) : Piece Pre Pub
    (fun s₀ s => ((NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)))) ∧
      decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)) = false)
    (fun s₀ s => IM s₀ i (G s₀ i (k + 2)) s ∧ fst s₀ i + k + 1 < bnd s₀ i) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hge := of_decide_eq_false hb
  have hb' := bnd_lt s₀ i
  obtain ⟨st, e, est⟩ := G_some hx (by omega)
  have hG : G s₀ i (k + 2) = none := by
    rw [G_next e, est, ite_pos' ⟨by omega, by rw [show fst s₀ i + k + 1 - 1 = fst s₀ i + k by omega]; omega⟩]
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨⟨hI.toPtr.keep k' (fun r hr => by simp at hr; simp [hr]) m, by rw [k'.gpr (by decide), hI.ebx],
      by rw [e1, hG]; rfl, by rw [hG]; exact SR.none _ _, hI.hi, hI.some, hI.fb, hI.bw⟩, hl⟩

theorem loop_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 1) s ∧ fst s₀ i + 1 < bnd s₀ i)
    (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) (.loop hbuNext .b) := by
  refine (loopC (NI i) (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) (fun s₀ => bnd s₀ i)
    (fun k s₀ => decide (idxOf (G s₀ i (k + 2)) < bnd s₀ i)) (fun k s₀ _ hc => ?_)
    (fun k s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) fun k => ?_).mono
    (fun s₀ s _ ⟨h, hl⟩ => ⟨h, by rw [G_one]; rfl, hl⟩) fun _ _ _ h => h
  · have hc := of_decide_eq_true hc
    have := bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega)
    omega
  refine Piece.seq (loads_piece i k) (Piece.seq (Piece.ite
    (fun s₀ => decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by simp only [fst, hq.ecur, hq.eyb]) (set2_piece i k) (fail2_piece i k))
    ((cmp_piece i (fun s₀ => G s₀ i (k + 2)) (fun s₀ => fst s₀ i + k + 1 < bnd s₀ i)).mono (fun _ _ _ h => h)
      fun s₀ s _ ⟨⟨h, hl⟩, hc⟩ => ⟨hc, fun hc' => ?_, fun hc' => ?_⟩))
  · have hc' := of_decide_eq_true hc'
    have := bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega)
    exact ⟨h, by omega, by omega⟩
  · have hc' := of_decide_eq_false hc'
    cases e : G s₀ i (k + 2) with
    | none =>
      have : G s₀ i (bnd s₀ i - fst s₀ i) = none := optFold_range_none _ (show k + 2 ≤ _ by omega) e
      rw [this]; rw [e] at h; exact h
    | some st =>
      have hx := G_idx s₀ i e
      rw [e] at hc'
      simp only [idxOf] at hc'
      rw [show bnd s₀ i - fst s₀ i = k + 2 by omega]; exact h

/-- The coefficients of polynomial `i`. -/
theorem coefs_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 0) s)
    (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) hbuCoefs := by
  have e0 : ∀ s₀, idxOf (G s₀ i 0) = fst s₀ i := fun _ => rfl
  refine Piece.seq ((cmp_piece i (fun s₀ => G s₀ i 0) (fun _ => True)).mono (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ h => h) (Piece.ite (fun s₀ => decide (idxOf (G s₀ i 0) < bnd s₀ i)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) ?_ ?_)
  · refine Piece.seq ((first_piece i).mono (fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, by
      have := of_decide_eq_true hb; rw [e0] at this; exact this⟩) fun _ _ _ h => h) ?_
    refine Piece.seq (addX (set1_piece i) fun _ _ _ h => h.1.2) (Piece.ite
      (fun s₀ => decide (fst s₀ i + 1 < bnd s₀ i)) (fun _ _ _ h => h.1.2)
      (fun s₀ s₀' _ _ hq => by simp only [fst, hq.ecur, hq.ebnd]) ?_ ?_)
    · exact (loop_piece i).mono (fun _ _ _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h
    · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, hl⟩, hb⟩ => by
        have := of_decide_eq_false hb
        rw [show bnd s₀ i - fst s₀ i = 1 by omega]; exact h
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => by
      have := of_decide_eq_false hb
      rw [e0] at this
      have := h.fb
      rw [show bnd s₀ i - fst s₀ i = 0 by omega]; exact h

end Up

end VG.Proof.MlDsa.X86.Pack.Hint
