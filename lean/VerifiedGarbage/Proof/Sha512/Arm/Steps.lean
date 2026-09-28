import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
import VerifiedGarbage.Proof.Sha512.Arm.Word64

/-!
# SHA-512 on ARMv7: the 64-bit operations

Untrusted: everything here is checked by Lean. Weakest-precondition rules
for the macros of `VG.Impl.Sha512.Arm` (loads and stores of a 64-bit word,
64-bit additions, constants, `Σ`/`σ`, `Ch` and `Maj`), each proved once for
any registers and offsets, in continuation-passing style: the rule for `x`
proves `WP (x ++ rest)` from a proof of `WP rest` for every state `x` can
end in.
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd WP.cons wp_mov wp_and wp_orr wp_ldr wp_str wp_rev op2_reg)

/-! ## States -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags). -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.refl (ds : List Reg) (s : State) : Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr, u.sp⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr, h.sp⟩

/-- The 64-bit word `x` is in the registers `l` (low half) and `h`. -/
def Pair (s : State) (l h : Reg) (x : BitVec 64) : Prop := s.gpr l = lo x ∧ s.gpr h = hi x

theorem Pair.of_only {ds : List Reg} {s s' : State} {l h : Reg} {x : BitVec 64} (p : Pair s l h x)
    (o : Only ds s s') (hl : l ∉ ds) (hh : h ∉ ds) : Pair s' l h x :=
  ⟨(o.gpr l hl).trans p.1, (o.gpr h hh).trans p.2⟩

/-! ## Memory -/

/-- The address `b + off`. -/
abbrev A (b : BitVec 32) (off : Nat) : Addr := State.addr (b + BitVec.ofNat 32 off)

/-- The 64-bit word at `b + off`, from its two halves. -/
def rd64 (m : Mem) (b : BitVec 32) (off : Nat) : BitVec 64 :=
  m.readW (A b (off + 4)) 32 ++ m.readW (A b off) 32

/-- Store the 64-bit word `x` at `b + off`, as its two halves. -/
def write64 (m : Mem) (b : BitVec 32) (off : Nat) (x : BitVec 64) : Mem :=
  (m.writeW (A b off) (lo x)).writeW (A b (off + 4)) (hi x)

theorem lo_rd64 (m : Mem) (b : BitVec 32) (off : Nat) : lo (rd64 m b off) = m.readW (A b off) 32 :=
  lo_append _ _

theorem hi_rd64 (m : Mem) (b : BitVec 32) (off : Nat) :
    hi (rd64 m b off) = m.readW (A b (off + 4)) 32 :=
  hi_append _ _

theorem mem_rd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Single instructions not covered by the SHA-256 rules -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_adds {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → s'.c = decide (2 ^ 32 ≤ (s.gpr n).toNat + y.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adds d n o :: is)) s Q :=
  WP.cons (s' := (addFlags s (s.gpr n) y).setReg d (s.gpr n + y)) (by simp [exec, ho])
    (k _ ⟨by simp [State.setReg], fun r h => by simp [State.setReg, addFlags, h], rfl, rfl, rfl, rfl⟩
      rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {v : BitVec 16}
    (k : ∀ s', Upd s s' d (v.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {v : BitVec 16}
    (k : ∀ s', Upd s s' d (v ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Loads, stores, additions and constants -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {l h b : Reg} {B : BitVec 32} {off : Nat} (hlb : l ≠ b) (hlh : l ≠ h)
    (ho : off + 4 < 4096) (hb : s.gpr b = B)
    (hi : InRegions s.wr (A B off) 4) (hi' : InRegions s.wr (A B (off + 4)) 4)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h (rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h b off ++ rest)) s Q := by
  simp only [ld, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) (mem_rd hi) fun s₁ u₁ => ?_
  refine wp_ldr ho (by rw [u₁.other b (Ne.symm hlb), hb]) (by rw [u₁.rd, u₁.wr]; exact mem_rd hi')
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, lo_rd64]
  · rw [u₂.gpr, u₁.mem, hi_rd64]

theorem wp_st {l h b : Reg} {B : BitVec 32} {off : Nat} {x : BitVec 64}
    (ho : off + 4 < 4096) (hb : s.gpr b = B) (hp : Pair s l h x)
    (hi : InRegions s.wr (A B off) 4) (hi' : InRegions s.wr (A B (off + 4)) 4)
    (k : ∀ s', Mupd s s' (write64 s.mem B off x) → WP isa (.block rest) s' Q) :
    WP isa (.block (st l h b off ++ rest)) s Q := by
  simp only [st, List.cons_append, List.nil_append]
  refine wp_str (by omega) (by rw [hb]) hi fun s₁ u₁ => ?_
  refine wp_str ho (by rw [u₁.gpr, hb]) (by rw [u₁.wr]; exact hi') fun s₂ u₂ =>
    k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

theorem carry_eq (a b : BitVec 32) :
    (if decide (2 ^ 32 ≤ a.toNat + b.toNat) = true then (1 : BitVec 32) else 0) =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  simp only [decide_eq_true_eq]

theorem wp_add64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64 dl dh l h ++ rest)) s Q := by
  simp only [add64, List.cons_append, List.nil_append]
  refine wp_adds (op2_reg _ _) fun s₁ u₁ hc => ?_
  refine wp_adc (op2_reg _ _) fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_add]
  · rw [u₂.gpr, hc, carry_eq, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.1, py.1, px.2,
      py.2, hi_add]

theorem movw_movt' (x : BitVec 32) :
    (x.extractLsb' 16 16 ++ ((x.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = x :=
  movw_movt x

theorem wp_const64 {l h : Reg} {x : BitVec 64} (hlh : l ≠ h)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h x → WP isa (.block rest) s' Q) :
    WP isa (.block (const64 l h x ++ rest)) s Q := by
  simp only [const64, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => wp_movw fun s₃ u₃ => wp_movt fun s₄ u₄ =>
    k s₄ ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄) |>.mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other l hlh, u₃.other l hlh, u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₄.gpr, u₃.gpr, movw_movt]

end

/-! ## Exclusive ors of shifted registers -/

/-- The value of an operand (`0` if it cannot be encoded). -/
def val (s : State) (o : Op2) : BitVec 32 := (o.eval s).getD 0

/-- An operand that is a shift of a register other than `d`, by an encodable amount. -/
def OkOp (d : Reg) : Op2 → Prop
  | .shifted r _ n => r ≠ d ∧ 1 ≤ n ∧ n ≤ 31
  | _ => False

theorem OkOp.eval {d : Reg} {o : Op2} (h : OkOp d o) {s s₀ : State}
    (hs : ∀ r, r ≠ d → s.gpr r = s₀.gpr r) : o.eval s = some (val s₀ o) := by
  match o, h with
  | .shifted r sh n, ⟨hr, h1, h2⟩ =>
    simp only [val, Op2.eval, h1, h2, and_self, ite_true, hs r hr, Option.getD_some]

section
variable {rest : List Instr} {Q : State → Prop}

theorem wp_eors {d : Reg} (s₀ : State) (ps : List Op2) (hp : ∀ p ∈ ps, OkOp d p) :
    ∀ (s : State) (acc : BitVec 32), (∀ r, r ≠ d → s.gpr r = s₀.gpr r) → s.gpr d = acc →
    (∀ s', Only [d] s s' → s'.gpr d = (ps.map (val s₀)).foldl (· ^^^ ·) acc →
      WP isa (.block rest) s' Q) →
    WP isa (.block (ps.map (fun p => Instr.dp .eor d d p) ++ rest)) s Q := by
  induction ps with
  | nil => intro s acc _ hd k; exact k s (Only.refl _ _) hd
  | cons p ps ih =>
    intro s acc hs hd k
    simp only [List.map_cons, List.cons_append]
    refine wp_eor ((hp p (by simp)).eval hs) fun s₁ u₁ => ?_
    refine ih (fun q hq => hp q (by simp [hq])) s₁ _ (fun r hr => by rw [u₁.other r hr, hs r hr])
      u₁.gpr fun s' o h => k s' ((Only.of_upd u₁).trans o |>.mono (by simp)) ?_
    rw [h, hd]; rfl

theorem wp_xorOf {d : Reg} (ps : List Op2) (hne : ps ≠ []) (hp : ∀ p ∈ ps, OkOp d p) (s : State)
    (k : ∀ s', Only [d] s s' → s'.gpr d = (ps.map (val s)).foldl (· ^^^ ·) 0 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorOf d ps ++ rest)) s Q := by
  match ps, hne with
  | p :: ps, _ =>
    simp only [xorOf, List.cons_append]
    refine wp_mov ((hp p (by simp)).eval (s₀ := s) fun _ _ => rfl) fun s₁ u₁ => ?_
    refine wp_eors s ps (fun q hq => hp q (by simp [hq])) s₁ _ (fun r hr => u₁.other r hr) u₁.gpr
      fun s' o h => k s' ((Only.of_upd u₁).trans o |>.mono (by simp)) ?_
    rw [h, List.map_cons, List.foldl_cons]
    congr 1
    simp

end

/-! ## `Σ₀`, `Σ₁`, `σ₀`, `σ₁` -/

theorem Op.okLo {l h d : Reg} (hl : l ≠ d) (hh : h ≠ d) {o : Op} (hv : o.valid = true) :
    ∀ p ∈ o.lo l h, OkOp d p := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.lo]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;>
      rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Op.lo, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩

theorem Op.okHi {l h d : Reg} (hl : l ≠ d) (hh : h ≠ d) {o : Op} (hv : o.valid = true) :
    ∀ p ∈ o.hi l h, OkOp d p := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.hi]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;>
      rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Op.hi, List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl; exact ⟨by assumption, by omega, by omega⟩

theorem Op.valLo (s : State) (l h : Reg) {o : Op} (hv : o.valid = true) :
    (o.lo l h).map (val s) = o.loVals (s.gpr l) (s.gpr h) := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.lo, Op.loVals]
    split
    · simp [val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
        show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]
    · simp [val, Op2.eval, show 1 ≤ n - 32 by omega, show n - 32 ≤ 31 by omega,
        show 1 ≤ 64 - n by omega, show 64 - n ≤ 31 by omega]
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Op.lo, Op.loVals, val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
      show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]

theorem Op.valHi (s : State) (l h : Reg) {o : Op} (hv : o.valid = true) :
    (o.hi l h).map (val s) = o.hiVals (s.gpr l) (s.gpr h) := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.hi, Op.hiVals]
    split
    · simp [val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
        show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]
    · simp [val, Op2.eval, show 1 ≤ n - 32 by omega, show n - 32 ≤ 31 by omega,
        show 1 ≤ 64 - n by omega, show 64 - n ≤ 31 by omega]
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Op.hi, Op.hiVals, val, Op2.eval, show 1 ≤ n by omega, show n ≤ 31 by omega]

theorem flatMap_ne_nil {ops : List Op} (h : ops ≠ []) (f : Op → List Op2)
    (hf : ∀ o, f o ≠ []) : ops.flatMap f ≠ [] := by
  match ops, h with
  | o :: _, _ => simp [hf o]

theorem Op.lo_ne_nil (l h : Reg) (o : Op) : o.lo l h ≠ [] := by
  cases o <;> simp only [Op.lo] <;> (try split) <;> simp

theorem Op.hi_ne_nil (l h : Reg) (o : Op) : o.hi l h ≠ [] := by
  cases o <;> simp only [Op.hi] <;> (try split) <;> simp

theorem map_val_lo (s : State) (l h : Reg) {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.lo l h)).map (val s) = ops.flatMap (Op.loVals (s.gpr l) (s.gpr h)) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, Op.valLo s l h (hv o (by simp)),
      ih fun o' h' => hv o' (by simp [h'])]

theorem map_val_hi (s : State) (l h : Reg) {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.hi l h)).map (val s) = ops.flatMap (Op.hiVals (s.gpr l) (s.gpr h)) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, Op.valHi s l h (hv o (by simp)),
      ih fun o' h' => hv o' (by simp [h'])]

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_sig {dl dh l h : Reg} {x : BitVec 64} {ops : List Op} (hne : ops ≠ [])
    (hv : ∀ o ∈ ops, o.valid = true) (hd : dl ≠ dh)
    (h₁ : l ≠ dl) (h₂ : h ≠ dl) (h₃ : l ≠ dh) (h₄ : h ≠ dh) (hp : Pair s l h x)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (evalOps x ops) → WP isa (.block rest) s' Q) :
    WP isa (.block (sig dl dh l h ops ++ rest)) s Q := by
  simp only [sig, List.append_assoc]
  refine wp_xorOf _ (flatMap_ne_nil hne _ (Op.lo_ne_nil l h))
    (fun p hp' => by
      obtain ⟨o, ho, hp'⟩ := List.mem_flatMap.mp hp'
      exact Op.okLo h₁ h₂ (hv o ho) p hp') s fun s₁ o₁ e₁ => ?_
  refine wp_xorOf _ (flatMap_ne_nil hne _ (Op.hi_ne_nil l h))
    (fun p hp' => by
      obtain ⟨o, ho, hp'⟩ := List.mem_flatMap.mp hp'
      exact Op.okHi h₃ h₄ (hv o ho) p hp') s₁ fun s₂ o₂ e₂ => k s₂ (o₁.trans o₂) ⟨?_, ?_⟩
  · rw [o₂.gpr dl (by simpa using hd), e₁, map_val_lo s l h hv, hp.1, hp.2, lo_evalOps x ops hv]
  · rw [e₂, map_val_hi s₁ l h hv, o₁.gpr l (by simpa using h₁), o₁.gpr h (by simpa using h₂), hp.1,
      hp.2, hi_evalOps x ops hv]

end

/-! ## `Ch` and `Maj` -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld1 {t b : Reg} {B : BitVec 32} {off : Nat} (ho : off < 4096) (hb : s.gpr b = B)
    (hi : InRegions s.wr (A B off) 4)
    (k : ∀ s', Only [t] s s' → s'.gpr t = s.mem.readW (A B off) 32 → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t b off :: rest)) s Q :=
  wp_ldr ho (by rw [hb]) (mem_rd hi) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_eor1 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n ^^^ s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .eor d n (.reg m) :: rest)) s Q :=
  wp_eor (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_and1 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n &&& s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .and d n (.reg m) :: rest)) s Q :=
  wp_and (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_orr1 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n ||| s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .orr d n (.reg m) :: rest)) s Q :=
  wp_orr (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

/-- The registers a region of 64-bit words can be addressed through: every
word `[B + o, B + o + 8)` with `o + 8 ≤ N` is writable. -/
def Reg64 (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 8 ≤ N → InRegions wr (A B o) 4 ∧ InRegions wr (A B (o + 4)) 4

theorem wp_ch {f g N : Nat} {B : BitVec 32} {e : BitVec 64} (hN : N ≤ 4096) (hf : f + 8 ≤ N)
    (hg : g + 8 ≤ N) (hR : Reg64 s.wr B N) (hb : s.gpr .r3 = B) (hp : Pair s X0 X1 e)
    (k : ∀ s', Only [Z0, Z1, X0] s s' →
      s'.gpr Z0 = lo (Spec.Sha512.ch e (rd64 s.mem B f) (rd64 s.mem B g)) →
      s'.gpr X0 = hi (Spec.Sha512.ch e (rd64 s.mem B f) (rd64 s.mem B g)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (chW f g ++ rest)) s Q := by
  simp only [chW, List.cons_append, List.nil_append]
  simp only [X0, X1, Z0, Z1] at hp k ⊢
  refine wp_ld1 (B := B) (by omega) hb (hR f hf).1 fun s₁ o₁ v₁ => ?_
  refine wp_ld1 (B := B) (by omega) (by rw [o₁.gpr _ (by decide), hb]) (by rw [o₁.wr]; exact (hR g hg).1)
    fun s₂ o₂ v₂ => ?_
  refine wp_eor1 fun s₃ o₃ v₃ => wp_and1 fun s₄ o₄ v₄ => wp_eor1 fun s₅ o₅ v₅ => ?_
  have O₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  refine wp_ld1 (B := B) (by omega) (by rw [O₅.gpr _ (by decide), hb]) (by rw [O₅.wr]; exact (hR f hf).2)
    fun s₆ o₆ v₆ => ?_
  refine wp_ld1 (B := B) (by omega) (by rw [o₆.gpr _ (by decide), O₅.gpr _ (by decide), hb])
    (by rw [o₆.wr, O₅.wr]; exact (hR g hg).2) fun s₇ o₇ v₇ => ?_
  refine wp_eor1 fun s₈ o₈ v₈ => wp_and1 fun s₉ o₉ v₉ => wp_eor1 fun s₁₀ o₁₀ v₁₀ => ?_
  have O := (((((O₅.trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀)
  refine k s₁₀ (O.mono (by decide)) ?_ ?_
  all_goals
    simp (disch := decide) only [o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr,
      o₂.gpr, o₁.gpr, v₁₀, v₉, v₈, v₇, v₆, v₅, v₄, v₃, v₂, v₁, o₆.mem, O₅.mem, o₁.mem, hp.1, hp.2,
      Proof.Sha512.ch_eq, lo_xor, lo_and, hi_xor, hi_and, lo_rd64, hi_rd64]

theorem wp_maj {b c N : Nat} {B : BitVec 32} {a : BitVec 64} (hN : N ≤ 4096) (hb' : b + 8 ≤ N)
    (hc : c + 8 ≤ N) (hR : Reg64 s.wr B N) (hb : s.gpr .r3 = B) (hp : Pair s X0 X1 a)
    (k : ∀ s', Only [Z0, Z1, X0, X1] s s' →
      s'.gpr Z0 = lo (Spec.Sha512.maj a (rd64 s.mem B b) (rd64 s.mem B c)) →
      s'.gpr X0 = hi (Spec.Sha512.maj a (rd64 s.mem B b) (rd64 s.mem B c)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (majW b c ++ rest)) s Q := by
  simp only [majW, List.cons_append, List.nil_append]
  simp only [X0, X1, Z0, Z1] at hp k ⊢
  refine wp_ld1 (B := B) (by omega) hb (hR b hb').1 fun s₁ o₁ v₁ => ?_
  refine wp_and1 fun s₂ o₂ v₂ => wp_orr1 fun s₃ o₃ v₃ => ?_
  refine wp_ld1 (B := B) (by omega) (by simp (disch := decide) only [o₃.gpr, o₂.gpr, o₁.gpr, hb])
    (by simp only [o₃.wr, o₂.wr, o₁.wr]; exact (hR c hc).1) fun s₄ o₄ v₄ => ?_
  refine wp_and1 fun s₅ o₅ v₅ => wp_orr1 fun s₆ o₆ v₆ => ?_
  refine wp_ld1 (B := B) (by omega)
    (by simp (disch := decide) only [o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr, o₂.gpr, o₁.gpr, hb])
    (by simp only [o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact (hR b hb').2) fun s₇ o₇ v₇ => ?_
  refine wp_and1 fun s₈ o₈ v₈ => wp_orr1 fun s₉ o₉ v₉ => ?_
  refine wp_ld1 (B := B) (by omega)
    (by simp (disch := decide) only [o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr, o₂.gpr,
      o₁.gpr, hb])
    (by simp only [o₉.wr, o₈.wr, o₇.wr, o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact (hR c hc).2)
    fun s₁₀ o₁₀ v₁₀ => ?_
  refine wp_and1 fun s₁₁ o₁₁ v₁₁ => wp_orr1 fun s₁₂ o₁₂ v₁₂ => ?_
  have O := (((((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans
    o₉).trans o₁₀).trans o₁₁).trans o₁₂)
  refine k s₁₂ (O.mono (by decide)) ?_ ?_
  all_goals
    simp (disch := decide) only [o₁₂.gpr, o₁₁.gpr, o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr,
      o₄.gpr, o₃.gpr, o₂.gpr, o₁.gpr, v₁₂, v₁₁, v₁₀, v₉, v₈, v₇, v₆, v₅, v₄, v₃, v₂, v₁,
      o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem, hp.1, hp.2,
      Proof.Sha512.maj_eq, lo_or, lo_and, hi_or, hi_and, lo_rd64, hi_rd64]

end

/-! ## The message schedule -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags), and memory `m`. -/
structure Wrote (ds : List Reg) (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.wrote {ds : List Reg} {s₁ s₂ s₃ : State} {m : Mem} (h : Only ds s₁ s₂) (u : Mupd s₂ s₃ m) :
    Wrote ds s₁ s₃ m :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadW {o N : Nat} {B : BitVec 32} (hN : N ≤ 4096) (ho : o + 8 ≤ N) (hR : Reg64 s.wr B N)
    (hb : s.gpr .r0 = B)
    (k : ∀ s', Wrote [X0, X1] s s' (write64 s.mem B o
      (rev (lo (rd64 s.mem B o)) ++ rev (hi (rd64 s.mem B o)))) → WP isa (.block rest) s' Q) :
    WP isa (.block (loadW o ++ rest)) s Q := by
  have e : loadW o ++ rest = ld X0 X1 .r0 o ++ (.rev X0 X0 :: .rev X1 X1 :: (st X1 X0 .r0 o ++ rest)) := rfl
  rw [e]
  refine wp_ld (by decide) (by decide) (by omega) hb (hR o ho).1 (hR o ho).2 fun s₁ o₁ p₁ => ?_
  refine wp_rev fun s₂ u₂ => wp_rev fun s₃ u₃ => ?_
  have O := (o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  refine wp_st (B := B) (x := rev (lo (rd64 s.mem B o)) ++ rev (hi (rd64 s.mem B o))) (by omega)
    (by rw [O.gpr _ (by decide), hb]) ⟨?_, ?_⟩ (by rw [O.wr]; exact (hR o ho).1)
    (by rw [O.wr]; exact (hR o ho).2) fun s₄ u₄ => k s₄ ?_
  · rw [u₃.gpr, u₂.other _ (by decide), p₁.2, lo_append]
  · rw [u₃.other _ (by decide), u₂.gpr, p₁.1, hi_append]
  · rw [O.mem] at u₄
    exact (O.mono (by decide)).wrote u₄

theorem wp_expandW {o2 o7 o15 o16 N : Nat} {B : BitVec 32} (hN : N ≤ 4096) (h2 : o2 + 8 ≤ N)
    (h7 : o7 + 8 ≤ N) (h15 : o15 + 8 ≤ N) (h16 : o16 + 8 ≤ N) (hR : Reg64 s.wr B N)
    (hb : s.gpr .r0 = B)
    (k : ∀ s', Wrote [X0, X1, Y0, Y1, Z0, Z1] s s' (write64 s.mem B o16
      (Spec.Sha512.ssig1 (rd64 s.mem B o2) + rd64 s.mem B o7 + Spec.Sha512.ssig0 (rd64 s.mem B o15) +
        rd64 s.mem B o16)) → WP isa (.block rest) s' Q) :
    WP isa (.block (expandW o2 o7 o15 o16 ++ rest)) s Q := by
  simp only [expandW, List.append_assoc]
  refine wp_ld (by decide) (by decide) (by omega) hb (hR o2 h2).1 (hR o2 h2).2 fun s₁ o₁ p₁ => ?_
  refine wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₁
    fun s₂ o₂ p₂ => ?_
  have O₂ := o₁.trans o₂
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), hb])
    (by rw [O₂.wr]; exact (hR o7 h7).1) (by rw [O₂.wr]; exact (hR o7 h7).2) fun s₃ o₃ p₃ => ?_
  refine wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
    fun s₄ o₄ p₄ => ?_
  have O₄ := (O₂.trans o₃).trans o₄
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₄.gpr _ (by decide), hb])
    (by rw [O₄.wr]; exact (hR o15 h15).1) (by rw [O₄.wr]; exact (hR o15 h15).2) fun s₅ o₅ p₅ => ?_
  refine wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₅
    fun s₆ o₆ p₆ => ?_
  refine wp_add64 (by decide) (by decide) ((p₄.of_only o₅ (by decide) (by decide)).of_only o₆
    (by decide) (by decide)) p₆ fun s₇ o₇ p₇ => ?_
  have O₇ := ((O₄.trans o₅).trans o₆).trans o₇
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₇.gpr _ (by decide), hb])
    (by rw [O₇.wr]; exact (hR o16 h16).1) (by rw [O₇.wr]; exact (hR o16 h16).2) fun s₈ o₈ p₈ => ?_
  refine wp_add64 (by decide) (by decide) (p₇.of_only o₈ (by decide) (by decide)) p₈
    fun s₉ o₉ p₉ => ?_
  have O₉ := (O₇.trans o₈).trans o₉
  refine wp_st (by omega) (by rw [O₉.gpr _ (by decide), hb]) p₉ (by rw [O₉.wr]; exact (hR o16 h16).1)
    (by rw [O₉.wr]; exact (hR o16 h16).2) fun s₁₀ u₁₀ => k s₁₀ ?_
  rw [O₉.mem] at u₁₀
  have e : ∀ m : Mem, m = s.mem → evalOps (rd64 m B o2) ssig1 + rd64 m B o7 +
      evalOps (rd64 m B o15) ssig0 + rd64 m B o16 = Spec.Sha512.ssig1 (rd64 s.mem B o2) +
      rd64 s.mem B o7 + Spec.Sha512.ssig0 (rd64 s.mem B o15) + rd64 s.mem B o16 := by
    rintro m rfl; rw [ssig1_eq, ssig0_eq]
  rw [O₂.mem, O₄.mem, O₇.mem, e _ rfl] at u₁₀
  exact (O₉.mono (by decide)).wrote u₁₀

end

/-! ## A round -/

/-- `T₁` of a round. -/
def T1 (e f g h k w : BitVec 64) : BitVec 64 :=
  h + Spec.Sha512.bsig1 e + Spec.Sha512.ch e f g + k + w

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_roundW {a b c d e f g h w : Nat} {k : BitVec 64} {B V : BitVec 32}
    (ha : a + 8 ≤ 64) (hb : b + 8 ≤ 64) (hc : c + 8 ≤ 64) (hd : d + 8 ≤ 64) (he : e + 8 ≤ 64)
    (hf : f + 8 ≤ 64) (hg : g + 8 ≤ 64) (hh : h + 8 ≤ 64) (hw : w + 8 ≤ 192)
    (hRB : Reg64 s.wr B 192) (hRV : Reg64 s.wr V 64) (h0 : s.gpr .r0 = B) (h3 : s.gpr .r3 = V)
    (K : ∀ s', Wrote [X0, X1, Y0, Y1, Z0, Z1, E0, E1] s s'
      (write64 (write64 s.mem V h
        (T1 (rd64 s.mem V e) (rd64 s.mem V f) (rd64 s.mem V g) (rd64 s.mem V h) k (rd64 s.mem B w) +
          (Spec.Sha512.bsig0 (rd64 s.mem V a) +
            Spec.Sha512.maj (rd64 s.mem V a) (rd64 s.mem V b) (rd64 s.mem V c))))
        V d (rd64 s.mem V d +
          T1 (rd64 s.mem V e) (rd64 s.mem V f) (rd64 s.mem V g) (rd64 s.mem V h) k (rd64 s.mem B w))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (roundW a b c d e f g h k w ++ rest)) s Q := by
  unfold roundW
  simp only [List.append_assoc]
  -- T₁
  refine wp_ld (by decide) (by decide) (by omega) h3 (hRV h hh).1 (hRV h hh).2 fun s₁ o₁ p₁ => ?_
  refine wp_ld (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3])
    (by rw [o₁.wr]; exact (hRV e he).1) (by rw [o₁.wr]; exact (hRV e he).2) fun s₂ o₂ p₂ => ?_
  rw [o₁.mem] at p₂
  refine wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₂
    fun s₃ o₃ p₃ => ?_
  refine wp_add64 (by decide) (by decide) ((p₁.of_only o₂ (by decide) (by decide)).of_only o₃
    (by decide) (by decide)) p₃ fun s₄ o₄ p₄ => ?_
  have O₄ := ((o₁.trans o₂).trans o₃).trans o₄
  have p₂' := (p₂.of_only o₃ (by decide) (by decide)).of_only o₄ (by decide) (by decide)
  refine wp_ch (N := 64) (by omega) hf hg (by rw [O₄.wr]; exact hRV) (by rw [O₄.gpr _ (by decide), h3])
    p₂' fun s₅ o₅ v₅ v₅' => ?_
  rw [O₄.mem] at v₅ v₅'
  refine wp_add64 (by decide) (by decide) (p₄.of_only o₅ (by decide) (by decide)) ⟨v₅, v₅'⟩
    fun s₆ o₆ p₆ => ?_
  refine wp_const64 (x := k) (by decide) fun s₇ o₇ p₇ => ?_
  refine wp_add64 (by decide) (by decide) (p₆.of_only o₇ (by decide) (by decide)) p₇
    fun s₈ o₈ p₈ => ?_
  have O₈ := (((O₄.trans o₅).trans o₆).trans o₇).trans o₈
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₈.gpr _ (by decide), h0])
    (by rw [O₈.wr]; exact (hRB w hw).1) (by rw [O₈.wr]; exact (hRB w hw).2) fun s₉ o₉ p₉ => ?_
  rw [O₈.mem] at p₉
  refine wp_add64 (by decide) (by decide) (p₈.of_only o₉ (by decide) (by decide)) p₉
    fun s₁₀ o₁₀ p₁₀ => ?_
  have O₁₀ := (O₈.trans o₉).trans o₁₀
  -- e' = d + T₁
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₁₀.gpr _ (by decide), h3])
    (by rw [O₁₀.wr]; exact (hRV d hd).1) (by rw [O₁₀.wr]; exact (hRV d hd).2) fun s₁₁ o₁₁ p₁₁ => ?_
  rw [O₁₀.mem] at p₁₁
  refine wp_add64 (by decide) (by decide) p₁₁ (p₁₀.of_only o₁₁ (by decide) (by decide))
    fun s₁₂ o₁₂ p₁₂ => ?_
  have O₁₂ := (O₁₀.trans o₁₁).trans o₁₂
  -- a' = T₁ + Σ₀(a) + Maj(a, b, c)
  refine wp_ld (by decide) (by decide) (by omega) (by rw [O₁₂.gpr _ (by decide), h3])
    (by rw [O₁₂.wr]; exact (hRV a ha).1) (by rw [O₁₂.wr]; exact (hRV a ha).2) fun s₁₃ o₁₃ p₁₃ => ?_
  rw [O₁₂.mem] at p₁₃
  refine wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₃
    fun s₁₄ o₁₄ p₁₄ => ?_
  have p₁₀' := ((p₁₀.of_only o₁₁ (by decide) (by decide)).of_only o₁₂ (by decide) (by decide)).of_only
    o₁₃ (by decide) (by decide) |>.of_only o₁₄ (by decide) (by decide)
  refine wp_add64 (by decide) (by decide) p₁₀' p₁₄ fun s₁₅ o₁₅ p₁₅ => ?_
  have O₁₅ := ((O₁₂.trans o₁₃).trans o₁₄).trans o₁₅
  have p₁₃' := (p₁₃.of_only o₁₄ (by decide) (by decide)).of_only o₁₅ (by decide) (by decide)
  refine wp_maj (N := 64) (by omega) hb hc (by rw [O₁₅.wr]; exact hRV) (by rw [O₁₅.gpr _ (by decide), h3])
    p₁₃' fun s₁₆ o₁₆ v₁₆ v₁₆' => ?_
  rw [O₁₅.mem] at v₁₆ v₁₆'
  refine wp_add64 (by decide) (by decide) (p₁₅.of_only o₁₆ (by decide) (by decide)) ⟨v₁₆, v₁₆'⟩
    fun s₁₇ o₁₇ p₁₇ => ?_
  have O₁₇ := (O₁₅.trans o₁₆).trans o₁₇
  have p₁₂' := (((((p₁₂.of_only o₁₃ (by decide) (by decide)).of_only o₁₄ (by decide) (by decide)).of_only
    o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide)).of_only o₁₇ (by decide) (by decide))
  -- Store them.
  refine wp_st (by omega) (by rw [O₁₇.gpr _ (by decide), h3]) p₁₇ (by rw [O₁₇.wr]; exact (hRV h hh).1)
    (by rw [O₁₇.wr]; exact (hRV h hh).2) fun s₁₈ u₁₈ => ?_
  refine wp_st (by omega) (by rw [u₁₈.gpr, O₁₇.gpr _ (by decide), h3])
    ⟨by rw [u₁₈.gpr]; exact p₁₂'.1, by rw [u₁₈.gpr]; exact p₁₂'.2⟩
    (by rw [u₁₈.wr, O₁₇.wr]; exact (hRV d hd).1) (by rw [u₁₈.wr, O₁₇.wr]; exact (hRV d hd).2)
    fun s₁₉ u₁₉ => K s₁₉ ⟨fun r hr => ?_, ?_, by rw [u₁₉.rd, u₁₈.rd, O₁₇.rd],
      by rw [u₁₉.wr, u₁₈.wr, O₁₇.wr], by rw [u₁₉.sp, u₁₈.sp, O₁₇.sp]⟩
  · rw [u₁₉.gpr, u₁₈.gpr]
    exact (O₁₇.mono (by decide)).gpr r hr
  · rw [u₁₉.mem, u₁₈.mem, O₁₇.mem]
    simp only [T1, bsig1_eq, bsig0_eq, BitVec.add_assoc]

end

end VG.Proof.Sha512.Arm
