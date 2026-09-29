import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Impl.MlKem.AArch64.Top

/-!
# ML-KEM-768 on AArch64: the hash routine

Untrusted: everything here is checked by Lean. `hash` (`Impl/MlKem/AArch64/Top.lean`)
computes the sponge of the concatenation of its input pieces, and writes
consecutive output to its output pieces (`hash_ok`): from the all-zero state
(`repr_nil`), each `absorb` continues the message from the position the
previous one returned, the padding, and each `squeeze` continues the output.
It changes only the Keccak state and working space, the outputs, the 16
bytes below the stack pointer, and registers that are not callee-saved (or
`x30`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Kept rs' s s' :=
  h.sub fun r hr => ⟨r, hs r hr, fun _ h => h⟩

/-- A block that writes no callee-saved register nor memory. -/
theorem Kept.of_keep {rs : List Region} {regs : List Reg} {s s' : State} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ preserved, r ∉ regs) : Kept rs s s' :=
  ⟨fun r hp _ => hk.gpr r (hr r hp), hk.sp, hk.rd, hk.wr, by rw [hm]; exact Frame.refl _ _⟩

theorem pres_not {r : Reg} (h : r ∈ preserved) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x9 := by
  revert r h; decide

/-! ## Addresses -/

theorem wp_ptrTo {d b : Reg} {off : Nat} (hd : d ≠ b) (ho : off < 65536) {is : List Instr} {s : State}
    {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → WP isa (.block is) s' Q) :
    WP isa (.block (ptrTo d b off ++ is)) s Q := by
  unfold ptrTo
  split
  · exact wp_addImm ‹_› k
  · refine wp_movz fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono (by simp)) ?_
    rw [e₂, h₁.get b (by simpa using hd.symm), e₁]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- `ptrTo` at the end of a block. -/
theorem wp_ptrTo' {d b : Reg} {off : Nat} (hd : d ≠ b) (ho : off < 65536) {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → Q s') :
    WP isa (.block (ptrTo d b off)) s Q := by
  rw [← List.append_nil (ptrTo d b off)]
  exact wp_ptrTo hd ho fun s' h e => wp_nil (k s' h e)

theorem wp_pos (first : Bool) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [.x2] s s' → (s'.gpr .x2).toNat = (if first then 0 else (s.gpr .x0).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block ((if first then [.movz .x .x2 0 0] else [mov .x2 .x0]) ++ is)) s Q := by
  cases first
  · exact wp_mov fun s' h e => k s' h (by rw [e]; rfl)
  · exact wp_movz fun s' h e => k s' h (by rw [e]; rfl)

theorem imm16 {v : Nat} (h : v < 65536) : ((BitVec.ofNat 16 v).setWidth 64).toNat = v := by
  rw [toNat_imm, BitVec.toNat_ofNat]; omega

/-! ## The setting -/

/-- A piece at `s`. -/
abbrev preg (s : State) (p : Piece) : Region := ⟨s.gpr p.base + BitVec.ofNat 64 p.off, p.len⟩

/-- Its bytes at `s`. -/
abbrev pbytes (s : State) (p : Piece) : List Byte := bytesAt s.mem (s.gpr p.base + BitVec.ofNat 64 p.off) p.len

/-- The Keccak state and working space at `sc + st` and `sc + wk`. -/
structure HSetup (sc : Reg) (st wk rate : Nat) (s₀ : State) : Prop where
  hsc : sc ∈ preserved ∧ sc ≠ .x30
  hst : st < 65536
  hwk : wk < 65536
  hrate : rate ∈ rates
  d : Region.Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩ ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
  sp16 : 16 ≤ s₀.sp.toNat
  kst : (stk s₀).Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩
  kwk : (stk s₀).Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
  cov : Covers [⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩, ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩] s₀.wr

section
variable (sc : Reg) (st wk : Nat) (s₀ : State)
abbrev STr : Region := ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩
abbrev WKr : Region := ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
end

/-- A piece the hash may read (`w = false`) or write (`w = true`). -/
structure PieceOk (sc : Reg) (st wk : Nat) (s₀ : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .x30
  off : p.off < 65536
  len : p.len < 65536
  dst : (preg s₀ p).Disjoint (STr sc st s₀)
  dwk : (preg s₀ p).Disjoint (WKr sc wk s₀)
  stk : (stk s₀).Disjoint (preg s₀ p)
  cov : Covers [preg s₀ p] (if w then s₀.wr else s₀.rd ++ s₀.wr)

theorem PieceOk.covW {sc : Reg} {st wk : Nat} {s₀ : State} {p : Piece} (h : PieceOk sc st wk s₀ true p) :
    Covers [preg s₀ p] s₀.wr := h.cov

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .x0).toNat

theorem rate_bounds {r : Nat} (h : r ∈ rates) : 0 < r ∧ r ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem stk_sp {s s' : State} (h : s.sp = s'.sp) : stk s = stk s' := by
  unfold stk; rw [h]

theorem below16 (sp : Addr) : below sp 16 = ⟨sp - 16, 16⟩ := rfl

theorem mem2' {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  rcases List.mem_cons.mp h with h | h
  · exact .inr (.inl h)
  · exact .inr (.inr (List.mem_singleton.mp h))

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem3 h)

theorem mem5 {α : Type} {a b c d e x : α} (h : x ∈ [a, b, c, d, e]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem4 h)

theorem mem6 {α : Type} {a b c d e f x : α} (h : x ∈ [a, b, c, d, e, f]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem5 h)

theorem mem7 {α : Type} {a b c d e f g x : α} (h : x ∈ [a, b, c, d, e, f, g]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f ∨ x = g := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem6 h)

theorem covers_one {R : Region} {rs : List Region} (h : R ∈ rs) : Covers [R] rs := fun _ _ hi => by
  obtain ⟨r, hr, hc⟩ := hi
  rw [List.mem_singleton.mp hr] at hc
  exact ⟨R, h, hc⟩

theorem covers_cons {R : Region} {rs xs : List Region} (h : Covers [R] xs) (h' : Covers rs xs) :
    Covers (R :: rs) xs := fun a n hi => by
  obtain ⟨r, hr, hc⟩ := hi
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h a n ⟨r, List.mem_singleton_self _, hc⟩
  · exact h' a n ⟨r, hr, hc⟩

theorem Covers.head {R : Region} {rs xs : List Region} (h : Covers (R :: rs) xs) : Covers [R] xs :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., hc⟩

theorem Covers.tail {R : Region} {rs xs : List Region} (h : Covers (R :: rs) xs) : Covers rs xs :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem covers_rw' {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => in_rd_wr (h a n hi)

/-! ## The absorbs -/

theorem absorbs_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : HSetup sc st wk rate s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk sc st wk s₀ false p) →
      Kept [STr sc st s₀, WKr sc wk s₀, below s₀.sp 16] s₀ s → Repr s.mem (s₀.gpr sc + BitVec.ofNat 64 st) rate msg →
      Pos first s = msg.length % rate →
      WP isa (absorbs sc st wk rate first ps) s fun s' =>
        Kept [STr sc st s₀, WKr sc wk s₀, below s₀.sp 16] s₀ s' ∧
        Repr s'.mem (s₀.gpr sc + BitVec.ofNat 64 st) rate (msg ++ (ps.map (pbytes s₀)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (pbytes s₀)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => wp_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have rpos := (rate_bounds hS.hrate).1
    have cs : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r := hk.cs
    have gsc := cs sc hS.hsc.1 hS.hsc.2
    have gb := cs p.base hp.base.1 hp.base.2
    have nsc := pres_not hS.hsc.1
    have nb := pres_not hp.base.1
    refine WP.seq ?_
    rw [keccakArgs, List.append_assoc, List.append_assoc, List.append_assoc]
    refine wp_pos first fun s₁ h₁ e₁ => wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₂ h₂ e₂ =>
      wp_movz fun s₃ h₃ e₃ => wp_ptrTo (Ne.symm nsc.2.2.2.2.2.1) hS.hwk fun s₄ h₄ e₄ => ?_
    refine wp_ptrTo (Ne.symm nb.2.2.2.1) hp.off fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
    have k₆ := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).keep
    have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    have hk₆ : Kept [STr sc st s₀, WKr sc wk s₀, below s₀.sp 16] s₀ s₆ :=
      hk.trans (Kept.of_keep k₆ m₆ (by decide))
    have sp₆ : s₆.sp = s₀.sp := hk₆.sp
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    have c0 : s₆.gpr .x0 = s₀.gpr sc + BitVec.ofNat 64 st := by
      rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c5 : s₆.gpr .x5 = s₀.gpr sc + BitVec.ofNat 64 wk := by
      rw [h₆.get .x5, h₅.get .x5, e₄, h₃.get sc (by simpa using nsc.2.1),
        h₂.get sc (by simpa using nsc.1), h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c3 : s₆.gpr .x3 = s₀.gpr p.base + BitVec.ofNat 64 p.off := by
      rw [h₆.get .x3, e₅, h₄.get p.base (by simpa using nb.2.2.2.2.2.1),
        h₃.get p.base (by simpa using nb.2.1), h₂.get p.base (by simpa using nb.1),
        h₁.get p.base (by simpa using nb.2.2.1), gb]
    refine WP.seq <| absorb_call (rate := rate) (pos := Pos first s) (len := p.len) c0
      (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; exact imm16 (by have := (rate_bounds hS.hrate).2; omega))
      (by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁]; cases first <;> rfl)
      c3 (by rw [e₆]; exact imm16 hp.len) c5 hS.hrate hpos' hS.d hp.dst hp.dwk (by rw [sp₆]; exact hS.sp16)
      (by rw [stk_sp sp₆]; exact hS.kst) (by rw [stk_sp sp₆]; exact hp.stk) (by rw [stk_sp sp₆]; exact hS.kwk)
      (by rw [hk₆.rd, hk₆.wr]; exact covers_cons hp.cov (covers_rw' hS.cov)) (by rw [hk₆.wr]; exact hS.cov)
      fun s₇ k₇ r₇ ret₇ => ?_
    rw [sp₆] at k₇
    have hk₇ := hk₆.trans k₇
    have eb : bytesAt s₆.mem (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = pbytes s₀ p :=
      bytesAt_frame hk₆.frame (fun r hr => by
        rcases mem3 hr with rfl | rfl | rfl
        · exact hp.dst
        · exact hp.dwk
        · rw [below16]; exact hp.stk.symm) (by have := hp.len; omega)
    have rep := r₇ msg (by rw [m₆]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₇ (msg ++ pbytes s₀ p)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₇ rep ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₇.gpr .x0).toNat = _
      rw [ret₇, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false,
        ← List.append_assoc] at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The registers and permissions `s₀` had. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : Rg s₀ s) (hk : Kept rs s s') : Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr h30 => by rw [hk.cs r hr h30, h.cs r hr h30]⟩

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (s₀ : State) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => bytesAt m (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = squeezeFrom rate P c p.len ∧
      Outs s₀ m rate P (c + p.len) ps

theorem squeezeFrom_shift {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) {S P : Spec.Sha3.State}
    {p c : Nat} (h : ∀ d, squeezeFrom rate S p d = squeezeFrom rate P c d) (a d : Nat) :
    squeezeFrom rate S (p + a) d = squeezeFrom rate P (c + a) d := by
  have e : ∀ (T : Spec.Sha3.State) (x : Nat), squeezeFrom rate T (x + a) d = (squeezeFrom rate T x (a + d)).drop a :=
    fun T x => by
      rw [← squeezeFrom_append hr hr' T x a d, List.drop_left' (VG.Proof.Sha3.length_squeezeFrom hr hr' T x a)]
  rw [e S p, e P c, h]

theorem squeezes_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : HSetup sc st wk rate s₀)
    {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, PieceOk sc st wk s₀ true p) → ps.Pairwise (fun p q => (preg s₀ p).Disjoint (preg s₀ q)) →
      Rg s₀ s → Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (s₀.gpr sc + BitVec.ofNat 64 st)) (Pos first s) d =
        squeezeFrom rate P c d) →
      WP isa (squeezes sc st wk rate first ps) s fun s' =>
        Kept (STr sc st s₀ :: WKr sc wk s₀ :: below s₀.sp 16 :: ps.map (preg s₀)) s s' ∧
        Outs s₀ s'.mem rate P c ps ∧ Rg s₀ s' := by
  intro ps
  induction ps with
  | nil => exact fun first s c _ _ hg _ _ => wp_nil ⟨Kept.refl _ _, trivial, hg⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have ⟨rpos, rle⟩ := rate_bounds hS.hrate
    have gsc := hg.cs sc hS.hsc.1 hS.hsc.2
    have gb := hg.cs p.base hp.base.1 hp.base.2
    have nsc := pres_not hS.hsc.1
    have nb := pres_not hp.base.1
    refine WP.seq ?_
    rw [keccakArgs, List.append_assoc, List.append_assoc, List.append_assoc]
    refine wp_pos first fun s₁ h₁ e₁ => wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₂ h₂ e₂ =>
      wp_movz fun s₃ h₃ e₃ => wp_ptrTo (Ne.symm nsc.2.2.2.2.2.1) hS.hwk fun s₄ h₄ e₄ => ?_
    refine wp_ptrTo (Ne.symm nb.2.2.2.1) hp.off fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
    have k₆ := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).keep
    have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    have kk₆ : Kept [] s s₆ := Kept.of_keep k₆ m₆ (by decide)
    have hg₆ := hg.kept kk₆
    have sp₆ : s₆.sp = s₀.sp := hg₆.sp
    have c0 : s₆.gpr .x0 = s₀.gpr sc + BitVec.ofNat 64 st := by
      rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c5 : s₆.gpr .x5 = s₀.gpr sc + BitVec.ofNat 64 wk := by
      rw [h₆.get .x5, h₅.get .x5, e₄, h₃.get sc (by simpa using nsc.2.1),
        h₂.get sc (by simpa using nsc.1), h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c3 : s₆.gpr .x3 = s₀.gpr p.base + BitVec.ofNat 64 p.off := by
      rw [h₆.get .x3, e₅, h₄.get p.base (by simpa using nb.2.2.2.2.2.1),
        h₃.get p.base (by simpa using nb.2.1), h₂.get p.base (by simpa using nb.1),
        h₁.get p.base (by simpa using nb.2.2.1), gb]
    refine WP.seq <| squeeze_call (rate := rate) (pos := Pos first s) (len := p.len) c0
      (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; exact imm16 (by omega))
      (by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁]; cases first <;> rfl)
      c3 (by rw [e₆]; exact imm16 hp.len) c5 hS.hrate hple hp.dst.symm hS.d hp.dwk
      (by rw [sp₆]; exact hS.sp16) (by rw [stk_sp sp₆]; exact hS.kst) (by rw [stk_sp sp₆]; exact hp.stk)
      (by rw [stk_sp sp₆]; exact hS.kwk)
      (by rw [hg₆.rd, hg₆.wr]; exact covers_rw' (covers_cons (Covers.head hS.cov) (covers_cons hp.covW (Covers.tail hS.cov))))
      (by rw [hg₆.wr]; exact covers_cons (Covers.head hS.cov) (covers_cons hp.covW (Covers.tail hS.cov)))
      fun s₇ k₇ b₇ r₇ n₇ => ?_
    rw [sp₆] at k₇
    have hg₇ := hg₆.kept k₇
    have out₇ : bytesAt s₇.mem (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = squeezeFrom rate P c p.len := by
      rw [b₇, m₆, hcont]
    have cont₇ : ∀ d, squeezeFrom rate (stateAt s₇.mem (s₀.gpr sc + BitVec.ofNat 64 st)) (Pos false s₇) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₇ = (s₇.gpr .x0).toNat from rfl, n₇, m₆]
      exact squeezeFrom_shift rpos (by omega) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    refine WP.mono (ih false s₇ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₇ r₇ cont₇)
      fun s' ⟨k', o', g'⟩ => ⟨?_, ⟨?_, o'⟩, g'⟩
    · refine (kk₆.mono (by simp)).trans ((k₇.mono fun r hr => ?_).trans (k'.mono fun r hr => ?_))
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        rcases mem2' hr with rfl | rfl
        · simp
        · simp
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        · simp [hr]
    · rw [← out₇]
      refine bytesAt_frame k'.frame (fun r hr => ?_) (by have := hp.len; omega)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp.dst
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp.dwk
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [below16]; exact hp.stk.symm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact pw.1 q hq

/-! ## The whole hash -/

theorem zstores_ok (B : Addr) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x0 = B →
      (∀ k < 25, InRegions s.wr (B + BitVec.ofNat 64 (8 * k)) 8) →
      WP isa (.block ((List.range n).map fun k => .str .x .x9 .x0 (8 * k))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        (∀ k < n, s'.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 = 0) ∧ Frame [⟨B, 200⟩] s.mem s'.mem := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | succ n ih =>
    intro hn s h9 h0 hin
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) h9 h0 hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := B + BitVec.ofNat 64 (8 * n)) (by constructor <;> omega) (by rw [g₁, h0])
      (by rw [w₁]; exact hin n (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      exact f₁.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))

theorem stateAt_zero' {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zeroState_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : HSetup sc st wk rate s₀)
    {s : State} (hg : Rg s₀ s) :
    WP isa (.block (zeroState sc st)) s fun s' =>
      Kept [STr sc st s₀] s s' ∧ stateAt s'.mem (s₀.gpr sc + BitVec.ofNat 64 st) = Spec.Sha3.zero := by
  have nsc := pres_not hS.hsc.1
  refine wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => ?_
  have hin : ∀ k < 25, InRegions s₂.wr (s₀.gpr sc + BitVec.ofNat 64 st + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k hk => by
      rw [h₂.wr, h₁.wr, hg.wr]
      obtain ⟨r, hr, hc⟩ := Covers.head hS.cov (s₀.gpr sc + BitVec.ofNat 64 st + BitVec.ofNat 64 (8 * k)) 8
        ⟨_, List.mem_singleton_self _, contains_off (by omega) (by decide)⟩
      exact ⟨r, hr, hc⟩
  refine WP.mono (zstores_ok _ 25 (by decide) (by rw [e₂]; rfl)
    (by rw [h₂.get .x0, e₁, hg.cs sc hS.hsc.1 hS.hsc.2]) hin) fun s' ⟨g', r', w', p', z', f'⟩ => ?_
  have k₂ := (h₁.trans h₂).keep
  refine ⟨⟨fun r hr h30 => ?_, by rw [p', k₂.sp], by rw [r', k₂.rd], by rw [w', k₂.wr], ?_⟩,
    stateAt_zero' fun k hk => z' k hk⟩
  · have := pres_not hr
    rw [g', k₂.gpr r (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨this.1, this.2.2.2.2.2.2⟩)]
  · rw [h₂.mem, h₁.mem] at f'; exact f'

theorem sfx8 {sfx : Nat} (h : sfx < 256) :
    ((BitVec.ofNat 16 sfx).setWidth 64).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, imm16 (by omega), BitVec.toNat_ofNat]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : HSetup sc st wk rate s₀) {sfx : Nat}
    (hsfx : sfx < 256) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk sc st wk s₀ false p) (hout : ∀ p ∈ outs, PieceOk sc st wk s₀ true p)
    (hpw : outs.Pairwise (fun p q => (preg s₀ p).Disjoint (preg s₀ q))) :
    WP isa (hash sc st wk rate sfx ins outs) s₀ fun s' =>
      Kept (STr sc st s₀ :: WKr sc wk s₀ :: below s₀.sp 16 :: outs.map (preg s₀)) s₀ s' ∧
      Outs s₀ s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (pbytes s₀)).flatten)) 0 outs := by
  have ⟨rpos, rle⟩ := rate_bounds hS.hrate
  have nsc := pres_not hS.hsc.1
  have g0 : Rg s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  refine WP.seq (WP.mono (zeroState_ok hS g0) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hS ins true s₁ [] hin (k₁.mono (by simp)) (repr_nil z₁)
    (by rfl)) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false, List.nil_append] at p₂
  rw [List.nil_append] at r₂
  refine WP.seq ?_
  rw [keccakArgs, List.append_assoc, List.append_assoc]
  refine wp_pos false fun s₃ h₃ e₃ => wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₄ h₄ e₄ =>
    wp_movz fun s₅ h₅ e₅ => wp_ptrTo (Ne.symm nsc.2.2.2.2.1) hS.hwk fun s₆ h₆ e₆ => wp_movz
    fun s₇ h₇ e₇ => wp_nil ?_
  have k₇ := ((((h₃.trans h₄).trans h₅).trans h₆).trans h₇).keep
  have m₇ : s₇.mem = s₂.mem := by rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem]
  have kk₇ : Kept [] s₂ s₇ := Kept.of_keep k₇ m₇ (by decide)
  have hg₇ := k₂.rg.kept kk₇
  have gsc := k₂.cs sc hS.hsc.1 hS.hsc.2
  have sp₇ : s₇.sp = s₀.sp := hg₇.sp
  refine WP.seq <| pad_call (st := s₀.gpr sc + BitVec.ofNat 64 st) (sc := s₀.gpr sc + BitVec.ofNat 64 wk)
    (rate := rate) (pos := (s₂.gpr .x0).toNat)
    (by rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, e₄, h₃.get sc (by simpa using nsc.2.2.1), gsc])
    (by rw [h₇.get .x1, h₆.get .x1, e₅]; exact imm16 (by omega))
    (by rw [h₇.get .x2, h₆.get .x2, h₅.get .x2, h₄.get .x2, e₃]; rfl)
    (by rw [h₇.get .x4, e₆, h₅.get sc (by simpa using nsc.2.1), h₄.get sc (by simpa using nsc.1),
      h₃.get sc (by simpa using nsc.2.2.1), gsc])
    hS.hrate (by have : (s₂.gpr .x0).toNat = _ := p₂; rw [this]; exact Nat.mod_lt _ rpos) hS.d
    (by rw [sp₇]; exact hS.sp16) (by rw [stk_sp sp₇]; exact hS.kst) (by rw [stk_sp sp₇]; exact hS.kwk)
    (by rw [hg₇.rd, hg₇.wr]; exact covers_rw' hS.cov) (by rw [hg₇.wr]; exact hS.cov) fun s₈ k₈ r₈ => ?_
  rw [sp₇] at k₈
  have st₈ := r₈ _ (by rw [m₇]; exact r₂) p₂
  rw [show (s₇.gpr .x3).setWidth 8 = BitVec.ofNat 8 sfx by rw [e₇]; exact sfx8 hsfx] at st₈
  have hg₈ := hg₇.kept k₈
  refine WP.mono (squeezes_ok hS (P := absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (pbytes s₀)).flatten))
    outs true s₈ 0 hout hpw hg₈ (Nat.zero_le _) (fun d => by rw [st₈]; rfl)) fun s' ⟨k', o', _⟩ => ⟨?_, o'⟩
  refine (k₂.mono fun r hr => ?_).trans ((kk₇.mono (by simp)).trans ((k₈.mono fun r hr => ?_).trans k'))
  · rcases mem3 hr with rfl | rfl | rfl <;> simp
  · rcases mem3 hr with rfl | rfl | rfl <;> simp

end VG.Proof.MlKem.AArch64
