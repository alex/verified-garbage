import VerifiedGarbage.Proof.MlKem.Arm.Lay
import VerifiedGarbage.Proof.MlKem.Arm.Extra

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine

Untrusted: everything here is checked by Lean. `hash`
(`Impl/MlKem/Arm/Top.lean`) computes the sponge of the concatenation of its
input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues
the message from the position the previous one returned, the padding, and
each `squeeze` continues the output. It changes only the Keccak state and
working space, the outputs, the 8 bytes below the stack pointer, and
registers that are not callee-saved (or `lr`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

theorem pres_ne {r : Reg} (h : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  revert r; decide

theorem enc200 : encodable (BitVec.ofNat 32 200) = true := by decide
theorem enc0 : encodable (BitVec.ofNat 32 0) = true := by decide

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved ∧ p.base ≠ .lr)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hoe : encodable (BitVec.ofNat 32 p.off) = true)
    (hle : encodable (BitVec.ofNat 32 p.len) = true) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s fun s' => Only s s' ∧
      s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
      s'.gpr .r2 = (if first then BitVec.ofNat 32 0 else s.gpr .r0) ∧
      s'.gpr .r3 = s.gpr p.base + BitVec.ofNat 32 p.off ∧ s'.gpr .r12 = BitVec.ofNat 32 p.len ∧
      s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  obtain ⟨n0, n1, n2, n3, n12⟩ := pres_ne hb.1 hb.2
  have nl := hb.2
  cases first <;>
  · run_block [keccakArgs, pieceArgs, ptrTo, hre, hoe, hle, enc200, enc0, n0, n1, n2, n3, n12, nl]
    refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
    obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
    simp only [m0, m1, m2, m3, m12, hl, ite_false]

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) :
    WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .r0 = s.gpr .r7 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧
        s'.gpr .r2 = s.gpr .r0 ∧ s'.gpr .r3 = BitVec.ofNat 32 sfx ∧ s'.gpr .lr = s.gpr .r7 + BitVec.ofNat 32 200 := by
  run_block [keccakArgs, ptrTo, hre, hse, enc200]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, m12⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, hl, ite_false]

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Ctx.sep00 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega

theorem Ctx.sep01 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 8) : sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : sepB sz a b = true) : sepB sz b a = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega

/-- The regions of the sponge functions: the state, the working space and the stack arguments. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (0, 200, 640), (1, 0, 8)]

theorem Ctx.kregs {L : Lay} {s : State} (hc : Ctx L s) :
    regA (L.ptr 0) 200 = L.R 0 0 200 ∧ regA (L.ptr 0 + BitVec.ofNat 32 200) 640 = L.R 0 200 640 ∧
      below s 8 = L.R 1 0 8 :=
  ⟨Lay.regA_zero _ _, hc.regAo (by decide) _, hc.bel⟩

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .lr
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : encodable (BitVec.ofNat 32 p.off) = true
  lenc : encodable (BitVec.ofNat 32 p.len) = true
  pos : 0 < p.len
  lt : p.off + p.len < 2 ^ 32
  sep : sepAll L.sizes (idx p.base, p.off, p.len) kRegs = true
  cov : (⟨State.addr (L.ptr (idx p.base)), L.size (idx p.base)⟩ : Region) ∈ (if w then s.wr else s.rd ++ s.wr)

/-- The region of a piece. -/
abbrev Lay.P (L : Lay) (idx : Reg → Nat) (p : Piece) : Region := L.R (idx p.base) p.off p.len

/-- The bytes of a piece. -/
abbrev Lay.pb (L : Lay) (idx : Reg → Nat) (m : Mem) (p : Piece) : List Byte :=
  bytesAt m (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len

theorem sepAll_head {sz : List Nat} {a w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz a (w :: W) = true) : sepB sz a w = true := by
  simp only [sepAll, List.all_cons, Bool.and_eq_true] at h; exact h.1

theorem sepB_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} (h : sepB sz (i, o, l) w = true) :
    i < sz.length ∧ o + l ≤ sz.getD i 0 := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

theorem PieceOk.bounds {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    idx p.base < L.sizes.length ∧ p.off + p.len ≤ L.size (idx p.base) :=
  sepB_bounds (sepAll_head h.sep)

theorem PieceOk.sepK {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    sepB L.sizes (idx p.base, p.off, p.len) (0, 0, 200) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (0, 200, 640) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 8) = true := by
  have := h.sep
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem PieceOk.regA {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : regA (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) p.len = L.P idx p :=
  Lay.regA_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega)

theorem RL_kRegs (L : Lay) : L.RL kRegs = [L.R 0 0 200, L.R 0 200 640, L.R 1 0 8] := rfl

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r0).toNat

theorem pos_r2 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 32 0 else s.gpr .r0) = BitVec.ofNat 32 (Pos first s) := by
  cases first
  · simp only [Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The registers and permissions of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : Rg s₀ s) (hk : Kept rs s s') : Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr hl => by rw [hk.cs r hr hl, h.cs r hr hl]⟩

theorem Rg.ctx {L : Lay} {s₀ s : State} (hc : Ctx L s₀) (h : Rg s₀ s) : Ctx L s :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r7 (by decide) (by decide), hc.r7], by rw [h.sp]; exact hc.sp8,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

theorem PieceOk.covR {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ false p)
    (hg : Rg s₀ s) : Covers [L.P idx p] (s.rd ++ s.wr) := by
  have := h.cov
  simp only [Bool.false_eq_true, ite_false] at this
  rw [hg.rd, hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.covW {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ true p)
    (hg : Rg s₀ s) : Covers [L.P idx p] s.wr := by
  have := h.cov
  simp only [ite_true] at this
  rw [hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.fit {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) : (L.ptr (idx p.base) + BitVec.ofNat 32 p.off).toNat + p.len ≤ 2 ^ 32 :=
  Lay.fit_off hL h.bounds.1 h.bounds.2 h.pos

theorem PieceOk.len32 {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p)
    (_hL : L.Ok) : p.len < 2 ^ 32 := by
  have := h.lt; omega

theorem PieceOk.addr {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (hL : L.Ok)
    (h : PieceOk L idx s w p) :
    State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off) = State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off :=
  Lay.addr_off hL h.bounds.1 (by have := h.bounds.2; have := h.pos; omega)

theorem covers_kregs {L : Lay} {s : State} (hc : Ctx L s) :
    Covers [regA (L.ptr 0) 200, regA (L.ptr 0 + BitVec.ofNat 32 200) 640] s.wr := by
  rw [hc.kregs.1, hc.kregs.2.1]
  exact covers_cons' (hc.cs (by decide)) (covers_cons' (hc.cs (by decide)) covers_nil')

/-! ## The absorbs -/

theorem absorbs_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk L idx s₀ false p) →
      Kept (L.RL kRegs) s₀ s → Repr s.mem (State.addr (L.ptr 0)) rate msg →
      Pos first s = msg.length % rate →
      WP isa (absorbs rate first ps) s fun s' =>
        Kept (L.RL kRegs) s₀ s' ∧
        Repr s'.mem (State.addr (L.ptr 0)) rate (msg ++ (ps.map (L.pb idx s₀.mem)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (L.pb idx s₀.mem)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have hcs := hk.rg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA : AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos', hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e0]; exact Lay.disj hL hp.sepK.1
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [er]; exact hp.covR hg₁
    refine WP.seq (absorb_ok hA fun s₂ k₂ r₂ ret₂ => ?_)
    rw [e0, e1, e2, ← RL_kRegs] at k₂
    have hk₂ : Kept (L.RL kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (State.addr (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem, hp.addr hL]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.len32 hL; omega)
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r0).toNat = _
      rw [ret₂, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The triple of a piece. -/
abbrev trip (idx : Reg → Nat) (p : Piece) : Nat × Nat × Nat := (idx p.base, p.off, p.len)

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (L : Lay) (idx : Reg → Nat) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => L.pb idx m p = squeezeFrom rate P c p.len ∧ Outs L idx m rate P (c + p.len) ps

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W = true) (h' : sepAll sz a W' = true) : sepAll sz a (W ++ W') = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩

theorem sepAll_map {α : Type} {sz : List Nat} {a : Nat × Nat × Nat} {ps : List α} {f : α → Nat × Nat × Nat}
    (h : ∀ q ∈ ps, sepB sz a (f q) = true) : sepAll sz a (ps.map f) = true := by
  simp only [sepAll, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem squeezes_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀ : State} (hc : Ctx L s₀) {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀ true p) → ps.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true) →
      Rg s₀ s → Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (State.addr (L.ptr 0))) (Pos first s) d = squeezeFrom rate P c d) →
      WP isa (squeezes rate first ps) s fun s' =>
        Kept (L.RL (kRegs ++ ps.map (trip idx))) s s' ∧ Outs L idx s'.mem rate P c ps := by
  intro ps
  induction ps with
  | nil => exact fun _ s _ _ _ _ _ _ => WP.block_nil ⟨Kept.refl _ _, trivial⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have rle := rates_lt hrate
    have hcs := hg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base.1 hp.base.2, hp.ptr]
    rw [hcs.r7] at g0 glr
    rw [gb] at g3
    rw [pos_r2] at g2
    obtain ⟨e0, e1, e2⟩ := hc₁.kregs
    have er := hp.regA hL
    have hg₁ : Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS : SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
        rate (Pos first s) p.len := by
      refine ⟨g0, g1, g2, g3, g12, glr, hrate, hple, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc.fit,
        hp.fit hL, hc.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
      · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
      · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
      · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
      · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
      · rw [e0, er, e1]
        exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg₁)
          (covers_cons' (hc₁.cs (by decide)) covers_nil'))
    refine WP.seq (squeeze_ok hS fun s₂ k₂ b₂ r₂ n₂ => ?_)
    rw [e0, er, e1, e2] at k₂
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (State.addr (L.ptr (idx p.base)) + BitVec.ofNat 64 p.off) p.len = _
      rw [← hp.addr hL, b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (State.addr (L.ptr 0))) (Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₂ = (s₂.gpr .r0).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (sepAll_append hp.sep (sepAll_map pw.1)) (by have := hp.len32 hL; omega)

/-! ## The whole hash -/

theorem zeroState_ok {L : Lay} {s : State} (hc : Ctx L s) :
    WP isa (.block (zeroState .r7)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (State.addr (L.ptr 0)) = Spec.Sha3.zero := by
  rw [zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = L.ptr 0 := by rw [g]; simp [State.setReg, hc.r7]
  refine WP.mono (Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; exact fit_le (by decide) hc.fit) fun k hk => by
      rw [e7, wr]
      exact hc.cs (o := 4 * k) (l := 4) (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7] at hf hz
  refine ⟨⟨fun r hr hl => ?_, by rw [h₂.sp, sp], by rw [h₂.rd, rd], by rw [h₂.wr, wr], ?_⟩,
    Sample.stateAt_zero hz⟩
  · rw [h₂.gpr, g]
    obtain ⟨-, -, -, -, n12⟩ := pres_ne hr hl
    simp [State.setReg, n12]
  · rw [← m]
    refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    show Region.Sub _ (L.R 0 0 200)
    rw [← Lay.regA_zero]; exact fun _ h => h

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 32 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sfx < 2 ^ 32)]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    (hsfx : sfx < 256) {s₀ : State} (hc : Ctx L s₀) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk L idx s₀ false p) (hout : ∀ p ∈ outs, PieceOk L idx s₀ true p)
    (hpw : outs.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true)) :
    WP isa (hash rate sfx ins outs) s₀ fun s' =>
      Kept (L.RL (kRegs ++ outs.map (trip idx))) s₀ s' ∧
      Outs L idx s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (L.pb idx s₀.mem)).flatten)) 0
        outs := by
  have hL := hc.ok
  have rpos := rate_pos hrate
  refine WP.seq (WP.mono (zeroState_ok hc) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hrate hre hc ins true s₁ [] hin (k₁.monoL (by simp)) (repr_nil z₁)
    (by simp [Pos])) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  have hc₂ := k₂.rg.ctx hc
  refine WP.seq (WP.mono (pargs_ok hre hse) fun s₃ ⟨o₃, g0, g1, g2, g3, glr⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.r7] at g0 glr
  obtain ⟨e0, e1, e2⟩ := hc₃.kregs
  have hP : PadArgs s₃ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate (s₂.gpr .r0).toNat (BitVec.ofNat 32 sfx) := by
    refine ⟨g0, g1, by rw [g2, BitVec.ofNat_toNat, BitVec.setWidth_eq], g3, glr, hrate,
      by rw [show (s₂.gpr .r0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos, hc₃.sp8,
      fit_le (by decide) hc.fit, hc.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₃⟩
    · rw [e0, e1]; exact Lay.disj hL (hc.sep00 (by decide) (by decide) (by decide))
    · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
    · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc.sep01 (by decide) (by decide)))
  refine WP.seq (pad_ok hP fun s₄ k₄ st₄ => ?_)
  rw [e0, e1, e2, ← RL_kRegs] at k₄
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [sfx8 hsfx] at st
  have hg₄ : Rg s₀ s₄ := (k₂.trans ((o₃.kept _).trans k₄)).rg
  refine WP.mono (squeezes_ok hrate hre hc outs true s₄ 0 hout hpw hg₄ (Nat.zero_le _)
    (fun d => by rw [st]; rfl)) fun s' ⟨k', o'⟩ => ⟨?_, o'⟩
  refine ((k₂.trans ((o₃.kept _).trans k₄)).monoL fun w hw => List.mem_append_left _ hw).trans k'

/-! ## The arguments of the sponge functions, for the constant-time proofs -/

theorem absorbArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, covers_kregs hc₁, ?_⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e0]; exact Lay.disj hL hp.sepK.1
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [er]; exact hp.covR hg

theorem squeezeArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hg : Rg s₀ s₁) (hp : PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 p.len)
    (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  have er := hp.regA hL
  refine ⟨g0, g1, g2, g3, g12, glr, hrate, hpos, hp.len32 hL, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hp.fit hL, hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, er]; exact Lay.disj hL (sepB_symm hp.sepK.1)
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [er, e1]; exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, er]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e0, er, e1]
    exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg)
      (covers_cons' (hc₁.cs (by decide)) covers_nil'))

theorem padArgs_of {L : Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) {sfx : BitVec 32}
    (g0 : s₁.gpr .r0 = L.ptr 0) (g1 : s₁.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 pos)
    (g3 : s₁.gpr .r3 = sfx) (glr : s₁.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200) :
    PadArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate pos sfx := by
  have hL := hc₁.ok
  obtain ⟨e0, e1, e2⟩ := hc₁.kregs
  refine ⟨g0, g1, g2, g3, glr, hrate, hpos, hc₁.sp8, fit_le (by decide) hc₁.fit,
    hc₁.fitO (by decide) (by decide), ?_, ?_, ?_, covers_kregs hc₁⟩
  · rw [e0, e1]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2, e1]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-- The 64 bytes of `G(c)` squeezed at once: both of its outputs. -/
theorem G_split (c : List Byte) :
    Spec.Sha3.squeezeFrom 72 (VG.Proof.MlKem.padded 72 Spec.Sha3.sha3Suffix c) 0 64 =
      (Spec.MlKem.G c).1 ++ (Spec.MlKem.G c).2 := by
  simp only [Spec.MlKem.G, VG.Proof.MlKem.sha3_512_eq, List.take_append_drop]

end VG.Proof.MlKem.Arm
