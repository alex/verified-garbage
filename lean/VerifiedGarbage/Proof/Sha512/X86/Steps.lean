import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Sha512.Arm.Word64
import VerifiedGarbage.Impl.Sha512.X86

/-!
# SHA-512 on x86 (32-bit): the 64-bit operations

Untrusted: everything here is checked by Lean. Weakest-precondition rules
for the macros of `VG.Impl.Sha512.X86` (loads and stores of a 64-bit word in
the scratch buffer, 64-bit additions, `Σ`/`σ`, `Ch` and `Maj`), each proved
once for any registers and offsets, in continuation-passing style: the rule
for `x` proves `WP (x ++ rest)` from a proof of `WP rest` for every state `x`
can end in. The halves of 64-bit values are those of the ARMv7 proof
(`Proof/Sha512/Arm/Word64.lean`), whose lemmas about them are about bit
vectors only.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_ sc T Y0 Y1 Z0 Z1 Op Part ld st add64 add64m add64i xorOf sig ch1 chW maj1
  majW loadW expandW roundW)
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.Sha512.Arm (lo_add hi_add lo_xor hi_xor lo_and hi_and lo_or hi_or lo_append hi_append
  hi_append_lo evalOps lo_evalOps hi_evalOps)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd WP.cons wp_store wp_bswap wp_shr)

theorem lo_eq (x : BitVec 64) : Impl.Sha512.X86.lo x = lo x := rfl
theorem hi_eq (x : BitVec 64) : Impl.Sha512.X86.hi x = hi x := rfl

/-! ## States -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags). -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.refl (ds : List Reg) (s : State) : Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr⟩

/-- The 64-bit word `x` is in the registers `l` (low half) and `h`. -/
def Pair (s : State) (l h : Reg) (x : BitVec 64) : Prop := s.gpr l = lo x ∧ s.gpr h = hi x

theorem Pair.of_only {s s' : State} {l h : Reg} {x : BitVec 64} {ds : List Reg} (p : Pair s l h x)
    (o : Only ds s s') (hl : l ∉ ds) (hh : h ∉ ds) : Pair s' l h x :=
  ⟨(o.gpr l hl).trans p.1, (o.gpr h hh).trans p.2⟩

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags), and memory `m`. -/
structure Wrote (ds : List Reg) (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.wrote {ds : List Reg} {s₁ s₂ s₃ : State} {m : Mem} (h : Only ds s₁ s₂) (u : Mupd s₂ s₃ m) :
    Wrote ds s₁ s₃ m :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, u.rd.trans h.rd, u.wr.trans h.wr⟩

theorem Wrote.mono' {ds es : List Reg} {s s' : State} {m : Mem} (w : Wrote ds s s' m)
    (h : ∀ r ∈ ds, r ∈ es) : Wrote es s s' m :=
  ⟨fun r hr => w.gpr r fun hd => hr (h r hd), w.mem, w.rd, w.wr⟩

/-! ## Memory -/

/-- The 64-bit word at `[b + off]`, from its two halves. -/
def rd64 (m : Mem) (b : BitVec 32) (off : Nat) : BitVec 64 :=
  m.readW (addr b (off + 4)) 32 ++ m.readW (addr b off) 32

/-- Store the 64-bit word `x` at `[b + off]`, as its two halves. -/
def write64 (m : Mem) (b : BitVec 32) (off : Nat) (x : BitVec 64) : Mem :=
  (m.writeW (addr b off) (lo x)).writeW (addr b (off + 4)) (hi x)

theorem lo_rd64 (m : Mem) (b : BitVec 32) (off : Nat) : lo (rd64 m b off) = m.readW (addr b off) 32 :=
  lo_append _ _

theorem hi_rd64 (m : Mem) (b : BitVec 32) (off : Nat) :
    hi (rd64 m b off) = m.readW (addr b (off + 4)) 32 :=
  hi_append _ _

theorem mem_rd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Every word `[B + o, B + o + 4)` with `o + 4 ≤ N` is writable. -/
def Acc (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 4 ≤ N → InRegions wr (addr B o) 4

/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ea_of {b : Reg} {B : BitVec 32} (hb : s.gpr b = B) (d : Nat) : s.ea (at_ b d) = addr B d := by
  rw [← hb]; rfl

theorem readSrc_mem {b : Reg} {d : Nat} {B : BitVec 32} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 4) :
    readSrc s (.mem (at_ b d)) = some (s.mem.readW (addr B d) 32) := by
  show s.load32 (s.ea (at_ b d)) = _
  rw [ea_of hb]; simp only [State.load32, hin, ↓reduceIte]

theorem wp_movS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, h]) (k _ (Upd.setReg _ _ _))

theorem wp_addS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_adcS {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xorS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_andS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_orS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_ror {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.setFlags _ _ _ _ _ _ _))

end

theorem carry_eq (a b : BitVec 32) :
    (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + b.toNat))).setWidth 32 =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- A left shift, as the code computes it: a rotation, masked. -/
theorem ror_and (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) :
    x.rotateRight (32 - n) &&& (BitVec.allOnes 32 <<< n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt (show 32 - n < 32 by omega)]
  by_cases hc : i < n
  · simp [hc, hi]
  · simp [hc, hi, show ¬ i < 32 - (32 - n) by omega, show i - (32 - (32 - n)) = i - n by omega]
    omega

/-! ## Loads, stores and additions of 64-bit words in the scratch buffer -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {l h : Reg} {B : BitVec 32} {off N : Nat} (hl : l ≠ .esi) (hlh : l ≠ h)
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h (rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h off ++ rest)) s Q := by
  simp only [ld, sc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hb (mem_rd (hA off (by omega)))) fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (by rw [u₁.other _ (Ne.symm hl), hb])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA (off + 4) (by omega)))) fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, lo_rd64]
  · rw [u₂.gpr, u₁.mem, hi_rd64]

theorem wp_st {l h : Reg} {B : BitVec 32} {off N : Nat} {x : BitVec 64}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N) (hp : Pair s l h x)
    (k : ∀ s', Mupd s s' (write64 s.mem B off x) → WP isa (.block rest) s' Q) :
    WP isa (.block (st l h off ++ rest)) s Q := by
  simp only [st, List.cons_append, List.nil_append]
  refine wp_store (ea_of hb _) (hA off (by omega)) fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.gpr, hb]) _) (by rw [u₁.wr]; exact hA (off + 4) (by omega))
    fun s₂ u₂ => k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

theorem wp_add64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64 dl dh l h ++ rest)) s Q := by
  simp only [add64, List.cons_append, List.nil_append]
  refine wp_addS rfl fun s₁ u₁ hc => ?_
  refine wp_adcS rfl hc fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_add]
  · rw [u₂.gpr, carry_eq, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.1, py.1, px.2,
      py.2, hi_add]

theorem wp_add64m {dl dh : Reg} {x : BitVec 64} {B : BitVec 32} {off N : Nat} (h₁ : dl ≠ dh)
    (h₂ : dl ≠ .esi) (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N) (px : Pair s dl dh x)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64m dl dh off ++ rest)) s Q := by
  simp only [add64m, sc, List.cons_append, List.nil_append]
  refine wp_addS (readSrc_mem hb (mem_rd (hA off (by omega)))) fun s₁ u₁ hc => ?_
  refine wp_adcS (readSrc_mem (by rw [u₁.other _ (Ne.symm h₂), hb])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA (off + 4) (by omega)))) hc fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, lo_add, lo_rd64]
  · rw [u₂.gpr, carry_eq, u₁.other dh (Ne.symm h₁), u₁.mem, px.1, px.2, hi_add, lo_rd64, hi_rd64]

theorem wp_add64i {dl dh : Reg} {x : BitVec 64} (h₁ : dl ≠ dh) (px : Pair s dl dh x) (y : BitVec 64)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64i dl dh y ++ rest)) s Q := by
  simp only [add64i, List.cons_append, List.nil_append]
  refine wp_addS rfl fun s₁ u₁ hc => ?_
  refine wp_adcS rfl hc fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, lo_add, lo_eq]
  · rw [u₂.gpr, carry_eq, u₁.other dh (Ne.symm h₁), px.1, px.2, hi_add, lo_eq, hi_eq]

end

/-! ## `Σ₀`, `Σ₁`, `σ₀`, `σ₁` -/

/-- A part's value, from the halves `L`, `H` of the word. -/
def partVal (L H : BitVec 32) : Part → BitVec 32
  | .shr h n => (if h then H else L) >>> n
  | .shl h n => (if h then H else L) <<< n

/-- The shift amounts the code can encode. -/
def partOk : Part → Bool
  | .shr _ n => 0 < n && n < 32
  | .shl _ n => 0 < n && n < 32

/-- The term, in the terms of the ARMv7 proof. -/
def _root_.VG.Impl.Sha512.X86.Op.arm : Op → Impl.Sha512.Arm.Op
  | .rotr n => .rotr n
  | .shr n => .shr n

theorem map_lo (L H : BitVec 32) (o : Op) : o.lo.map (partVal L H) = o.arm.loVals L H := by
  cases o with
  | rotr n => simp only [Op.lo, Op.arm, Impl.Sha512.Arm.Op.loVals]; split <;> simp [partVal]
  | shr n => simp [Op.lo, Op.arm, Impl.Sha512.Arm.Op.loVals, partVal]

theorem map_hi (L H : BitVec 32) (o : Op) : o.hi.map (partVal L H) = o.arm.hiVals L H := by
  cases o with
  | rotr n => simp only [Op.hi, Op.arm, Impl.Sha512.Arm.Op.hiVals]; split <;> simp [partVal]
  | shr n => simp [Op.hi, Op.arm, Impl.Sha512.Arm.Op.hiVals, partVal]

theorem map_flatMap_lo (L H : BitVec 32) (ops : List Op) :
    (ops.flatMap Op.lo).map (partVal L H) = (ops.map Op.arm).flatMap (Impl.Sha512.Arm.Op.loVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih => rw [List.flatMap_cons, List.map_append, map_lo, ih]; rfl

theorem map_flatMap_hi (L H : BitVec 32) (ops : List Op) :
    (ops.flatMap Op.hi).map (partVal L H) = (ops.map Op.arm).flatMap (Impl.Sha512.Arm.Op.hiVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih => rw [List.flatMap_cons, List.map_append, map_hi, ih]; rfl

section
variable {rest : List Instr} {Q : State → Prop}

theorem wp_part {d : Reg} {B : BitVec 32} {off N : Nat} {p : Part} (hp : partOk p = true)
    {s : State} (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', Only [d] s s' →
      s'.gpr d = partVal (s.mem.readW (addr B off) 32) (s.mem.readW (addr B (off + 4)) 32) p →
      WP isa (.block rest) s' Q) :
    WP isa (.block (p.load d off ++ rest)) s Q := by
  have hin : ∀ h : Bool, InRegions (s.rd ++ s.wr) (addr B (if h then off + 4 else off)) 4 := fun h => by
    cases h <;> exact mem_rd (hA _ (by simp only [Bool.false_eq_true, ite_false, ite_true]; omega))
  have hv : ∀ h : Bool, s.mem.readW (addr B (if h then off + 4 else off)) 32 =
      if h then s.mem.readW (addr B (off + 4)) 32 else s.mem.readW (addr B off) 32 := fun h => by
    cases h <;> rfl
  cases p with
  | shr h n =>
    simp only [partOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [Part.load, sc, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_mem hb (hin h)) fun s₁ u₁ => wp_shr ⟨by omega, by omega⟩ fun s₂ u₂ =>
      k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂) |>.mono (by simp)) ?_
    rw [u₂.gpr, u₁.gpr, hv]; simp only [partVal]
  | shl h n =>
    simp only [partOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [Part.load, sc, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_mem hb (hin h)) fun s₁ u₁ => wp_ror ⟨by omega, by omega⟩ fun s₂ u₂ =>
      wp_andS rfl fun s₃ u₃ =>
      k s₃ (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃) |>.mono (by simp)) ?_
    rw [u₃.gpr, u₂.gpr, u₁.gpr, hv, ror_and _ hp.1 hp.2]; simp only [partVal]

theorem foldl_xor_acc (a : BitVec 32) (l : List (BitVec 32)) :
    l.foldl (· ^^^ ·) a = a ^^^ l.foldl (· ^^^ ·) 0 :=
  VG.Proof.Sha512.Arm.foldl_xor_acc a l

theorem wp_xorRest {d : Reg} {B : BitVec 32} {off N : Nat} (hd : d ≠ .esi) (hdT : d ≠ T)
    (L H : BitVec 32) (ps : List Part) (hp : ∀ p ∈ ps, partOk p = true) :
    ∀ (s : State) (acc : BitVec 32), s.gpr .esi = B → Acc s.wr B N → off + 8 ≤ N →
    s.mem.readW (addr B off) 32 = L → s.mem.readW (addr B (off + 4)) 32 = H → s.gpr d = acc →
    (∀ s', Only [d, T] s s' → s'.gpr d = (ps.map (partVal L H)).foldl (· ^^^ ·) acc →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((ps.flatMap fun p => p.load T off ++ [.alu .xor d (.reg T)]) ++ rest)) s Q := by
  induction ps with
  | nil => intro s acc _ _ _ _ _ hd k; exact k s (Only.refl _ _) hd
  | cons p ps ih =>
    intro s acc hb hA ho hL hH hacc k
    simp only [List.flatMap_cons, List.append_assoc]
    refine wp_part (hp p (by simp)) hb hA ho fun s₁ o₁ v₁ => ?_
    refine wp_xorS rfl fun s₂ u₂ => ?_
    have O := (o₁.trans (Only.of_upd u₂))
    refine ih (fun q hq => hp q (by simp [hq])) s₂ _ (by rw [O.gpr _ (by simp [T, Ne.symm hd]), hb])
      (by rw [O.wr]; exact hA) ho (by rw [O.mem, hL]) (by rw [O.mem, hH]) rfl
      fun s' o h => k s' ((O.trans o).mono (by simp)) ?_
    rw [h, u₂.gpr, v₁, hL, hH, o₁.gpr d (by simpa using hdT), hacc]; rfl

theorem wp_xorOf {d : Reg} {B : BitVec 32} {off N : Nat} (hd : d ≠ .esi) (hdT : d ≠ T)
    (ps : List Part) (hne : ps ≠ []) (hp : ∀ p ∈ ps, partOk p = true) (s : State)
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', Only [d, T] s s' →
      s'.gpr d = (ps.map (partVal (s.mem.readW (addr B off) 32)
        (s.mem.readW (addr B (off + 4)) 32))).foldl (· ^^^ ·) 0 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorOf d off ps ++ rest)) s Q := by
  match ps, hne with
  | p :: ps, _ =>
    simp only [xorOf, List.append_assoc]
    refine wp_part (hp p (by simp)) hb hA ho fun s₁ o₁ v₁ => ?_
    refine wp_xorRest hd hdT _ _ ps (fun q hq => hp q (by simp [hq])) s₁ _ (by rw [o₁.gpr _ (by simp [Ne.symm hd]), hb])
      (by rw [o₁.wr]; exact hA) ho (by rw [o₁.mem]) (by rw [o₁.mem]) v₁
      fun s' o h => k s' ((o₁.trans o).mono (by simp)) ?_
    rw [h, List.map_cons, List.foldl_cons]
    exact congrArg (fun a => List.foldl _ a _) (by simp)

theorem flatMap_ne_nil {ops : List Op} (h : ops ≠ []) (f : Op → List Part)
    (hf : ∀ o, f o ≠ []) : ops.flatMap f ≠ [] := by
  match ops, h with
  | o :: _, _ => simp [hf o]

theorem Op.lo_ne_nil (o : Op) : o.lo ≠ [] := by
  cases o <;> simp only [Op.lo] <;> (try split) <;> simp

theorem Op.hi_ne_nil (o : Op) : o.hi ≠ [] := by
  cases o <;> simp only [Op.hi] <;> (try split) <;> simp

/-- A list of terms the code can compute. -/
def OpsOk (ops : List Op) : Prop :=
  ops ≠ [] ∧ (∀ p ∈ ops.flatMap Op.lo, partOk p = true) ∧ (∀ p ∈ ops.flatMap Op.hi, partOk p = true) ∧
    ∀ o ∈ ops.map Op.arm, Impl.Sha512.Arm.Op.valid o = true

theorem wp_sig {dl dh : Reg} {B : BitVec 32} {off N : Nat} {ops : List Op} (hok : OpsOk ops)
    (hd : dl ≠ dh) (h₁ : dl ≠ .esi) (h₂ : dh ≠ .esi) (h₃ : dl ≠ T) (h₄ : dh ≠ T)
    {s : State} (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', Only [dl, dh, T] s s' → Pair s' dl dh (evalOps (rd64 s.mem B off) (ops.map Op.arm)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (sig dl dh off ops ++ rest)) s Q := by
  obtain ⟨hne, hlo, hhi, hv⟩ := hok
  simp only [sig, List.append_assoc]
  refine wp_xorOf h₁ h₃ _ (flatMap_ne_nil hne _ Op.lo_ne_nil) hlo s hb hA ho fun s₁ o₁ e₁ => ?_
  refine wp_xorOf h₂ h₄ _ (flatMap_ne_nil hne _ Op.hi_ne_nil) hhi s₁ (by rw [o₁.gpr _ (by simp [T, Ne.symm h₁]), hb])
    (by rw [o₁.wr]; exact hA) ho fun s₂ o₂ e₂ => k s₂ ((o₁.trans o₂).mono (by simp)) ⟨?_, ?_⟩
  · rw [o₂.gpr dl (by simp [hd, h₃]), e₁, map_flatMap_lo, ← lo_rd64, ← hi_rd64,
      lo_evalOps _ _ hv]
  · rw [e₂, map_flatMap_hi, o₁.mem, ← lo_rd64, ← hi_rd64, hi_evalOps _ _ hv]

theorem bsig0_ok : OpsOk Impl.Sha512.X86.bsig0 := ⟨by decide, by decide, by decide, by decide⟩
theorem bsig1_ok : OpsOk Impl.Sha512.X86.bsig1 := ⟨by decide, by decide, by decide, by decide⟩
theorem ssig0_ok : OpsOk Impl.Sha512.X86.ssig0 := ⟨by decide, by decide, by decide, by decide⟩
theorem ssig1_ok : OpsOk Impl.Sha512.X86.ssig1 := ⟨by decide, by decide, by decide, by decide⟩

theorem bsig0_eq (x : BitVec 64) :
    Spec.Sha512.bsig0 x = evalOps x (Impl.Sha512.X86.bsig0.map Op.arm) :=
  VG.Proof.Sha512.Arm.bsig0_eq x
theorem bsig1_eq (x : BitVec 64) :
    Spec.Sha512.bsig1 x = evalOps x (Impl.Sha512.X86.bsig1.map Op.arm) :=
  VG.Proof.Sha512.Arm.bsig1_eq x
theorem ssig0_eq (x : BitVec 64) :
    Spec.Sha512.ssig0 x = evalOps x (Impl.Sha512.X86.ssig0.map Op.arm) :=
  VG.Proof.Sha512.Arm.ssig0_eq x
theorem ssig1_eq (x : BitVec 64) :
    Spec.Sha512.ssig1 x = evalOps x (Impl.Sha512.X86.ssig1.map Op.arm) :=
  VG.Proof.Sha512.Arm.ssig1_eq x

end

/-! ## `Ch` and `Maj` -/

section
variable {rest : List Instr} {Q : State → Prop}

theorem wp_ch1 {d : Reg} {B : BitVec 32} {e f g N : Nat} (hd : d ≠ .esi) {s : State}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (he : e + 4 ≤ N) (hf : f + 4 ≤ N) (hg : g + 4 ≤ N)
    (k : ∀ s', Only [d] s s' →
      s'.gpr d = (s.mem.readW (addr B f) 32 ^^^ s.mem.readW (addr B g) 32) &&&
        s.mem.readW (addr B e) 32 ^^^ s.mem.readW (addr B g) 32 → WP isa (.block rest) s' Q) :
    WP isa (.block (ch1 d e f g ++ rest)) s Q := by
  simp only [ch1, sc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hb (mem_rd (hA f hf))) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [u₁.other _ (Ne.symm hd), hb]
  refine wp_xorS (readSrc_mem b₁ (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA g hg))) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .esi = B := by rw [u₂.other _ (Ne.symm hd), b₁]
  refine wp_andS (readSrc_mem b₂ (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hA e he)))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .esi = B := by rw [u₃.other _ (Ne.symm hd), b₂]
  refine wp_xorS (readSrc_mem b₃ (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hA g hg)))
    fun s₄ u₄ => k s₄ ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄) |>.mono (by simp)) ?_
  rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]

theorem wp_ch {B : BitVec 32} {e f g N : Nat} {s : State}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (he : e + 8 ≤ N) (hf : f + 8 ≤ N) (hg : g + 8 ≤ N)
    (k : ∀ s', Only [Z0, Z1] s s' →
      Pair s' Z0 Z1 (Spec.Sha512.ch (rd64 s.mem B e) (rd64 s.mem B f) (rd64 s.mem B g)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (chW e f g ++ rest)) s Q := by
  simp only [chW, List.append_assoc]
  refine wp_ch1 (by decide) hb hA (by omega) (by omega) (by omega) fun s₁ o₁ v₁ => ?_
  refine wp_ch1 (by decide) (by rw [o₁.gpr _ (by decide), hb]) (by rw [o₁.wr]; exact hA)
    (by omega) (by omega) (by omega) fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono (by simp)) ⟨?_, ?_⟩
  · rw [o₂.gpr _ (by decide), v₁, Proof.Sha512.ch_eq, lo_xor, lo_and, lo_xor, lo_rd64, lo_rd64, lo_rd64]
  · rw [v₂, o₁.mem, Proof.Sha512.ch_eq, hi_xor, hi_and, hi_xor, hi_rd64, hi_rd64, hi_rd64]

theorem wp_maj1 {d : Reg} {B : BitVec 32} {a b c N : Nat} (hd : d ≠ .esi) (hdT : d ≠ T) {s : State}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ha : a + 4 ≤ N) (hb' : b + 4 ≤ N) (hc : c + 4 ≤ N)
    (k : ∀ s', Only [d, T] s s' →
      s'.gpr d = (s.mem.readW (addr B a) 32 ||| s.mem.readW (addr B b) 32) &&&
        s.mem.readW (addr B c) 32 ||| s.mem.readW (addr B a) 32 &&& s.mem.readW (addr B b) 32 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (maj1 d a b c ++ rest)) s Q := by
  simp only [maj1, sc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hb (mem_rd (hA a ha))) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [u₁.other _ (Ne.symm hd), hb]
  refine wp_orS (readSrc_mem b₁ (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA b hb'))) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .esi = B := by rw [u₂.other _ (Ne.symm hd), b₁]
  refine wp_andS (readSrc_mem b₂ (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hA c hc)))
    fun s₃ u₃ => ?_
  have O₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have b₃ : s₃.gpr .esi = B := by rw [O₃.gpr _ (by simp [Ne.symm hd]), hb]
  refine wp_movS (readSrc_mem b₃ (by rw [O₃.rd, O₃.wr]; exact mem_rd (hA a ha))) fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .esi = B := by rw [u₄.other _ (by decide), b₃]
  refine wp_andS (readSrc_mem b₄ (by rw [u₄.rd, u₄.wr, O₃.rd, O₃.wr]; exact mem_rd (hA b hb')))
    fun s₅ u₅ => wp_orS rfl fun s₆ u₆ =>
      k s₆ (((O₃.trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆) |>.mono
        (by simp)) ?_
  rw [u₆.gpr, u₅.other _ hdT, u₄.other _ hdT, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₄.mem, O₃.mem,
    u₂.mem, u₁.mem]

theorem wp_maj {B : BitVec 32} {a b c N : Nat} {s : State}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ha : a + 8 ≤ N) (hb' : b + 8 ≤ N) (hc : c + 8 ≤ N)
    (k : ∀ s', Only [Z0, Z1, T] s s' →
      Pair s' Z0 Z1 (Spec.Sha512.maj (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (majW a b c ++ rest)) s Q := by
  simp only [majW, List.append_assoc]
  refine wp_maj1 (by decide) (by decide) hb hA (by omega) (by omega) (by omega) fun s₁ o₁ v₁ => ?_
  refine wp_maj1 (by decide) (by decide) (by rw [o₁.gpr _ (by decide), hb]) (by rw [o₁.wr]; exact hA)
    (by omega) (by omega) (by omega) fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono (by simp)) ⟨?_, ?_⟩
  · rw [o₂.gpr _ (by decide), v₁, Proof.Sha512.maj_eq, lo_or, lo_and, lo_or, lo_and, lo_rd64, lo_rd64,
      lo_rd64]
  · rw [v₂, o₁.mem, Proof.Sha512.maj_eq, hi_or, hi_and, hi_or, hi_and, hi_rd64, hi_rd64, hi_rd64]

end

/-! ## 64-bit words in memory -/

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_self (m : Mem) {b : BitVec 32} {o : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) : rd64 (write64 m b o x) b o = x := by
  simp only [rd64, write64]
  rw [Mem.readW_writeW_self32, readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self32, hi_append_lo]

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    rd64 (write64 m b o x) b o' = rd64 m b o' := by
  simp only [rd64, write64]
  rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega)]

/-! ## The message schedule -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadW {i o N : Nat} {Bb B : BitVec 32} (ho : o + 8 ≤ N)
    (hA : Acc s.wr B N) (hb : s.gpr .esi = B) (hbb : s.gpr .edi = Bb)
    (hin : InRegions (s.rd ++ s.wr) (addr Bb i) 4) (hin' : InRegions (s.rd ++ s.wr) (addr Bb (i + 4)) 4)
    (k : ∀ s', Wrote [Z0, Z1] s s' (write64 s.mem B o
      (bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadW i o ++ rest)) s Q := by
  simp only [loadW, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hbb hin') fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (by rw [u₁.other _ (by decide), hbb]) (by rw [u₁.rd, u₁.wr]; exact hin))
    fun s₂ u₂ => wp_bswap fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  have O := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  refine wp_st (x := bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))
    (by rw [O.gpr _ (by decide), hb]) (by rw [O.wr]; exact hA) ho ⟨?_, ?_⟩ fun s₅ u₅ => k s₅ ?_
  · rw [lo_append, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [hi_append, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem]
  · rw [O.mem] at u₅
    exact (O.mono (by decide)).wrote u₅

theorem wp_expandW {o2 o7 o15 o16 N : Nat} {B : BitVec 32} (h2 : o2 + 8 ≤ N)
    (h7 : o7 + 8 ≤ N) (h15 : o15 + 8 ≤ N) (h16 : o16 + 8 ≤ N) (hA : Acc s.wr B N)
    (hb : s.gpr .esi = B)
    (k : ∀ s', Wrote [Y0, Y1, Z0, Z1, T] s s' (write64 s.mem B o16
      (Spec.Sha512.ssig1 (rd64 s.mem B o2) + rd64 s.mem B o7 + Spec.Sha512.ssig0 (rd64 s.mem B o15) +
        rd64 s.mem B o16)) → WP isa (.block rest) s' Q) :
    WP isa (.block (expandW o2 o7 o15 o16 ++ rest)) s Q := by
  simp only [expandW, List.append_assoc]
  refine wp_sig ssig1_ok (by decide) (by decide) (by decide) (by decide) (by decide) hb hA h2
    fun s₁ o₁ p₁ => ?_
  refine wp_add64m (by decide) (by decide) (by rw [o₁.gpr _ (by decide), hb]) (by rw [o₁.wr]; exact hA)
    h7 p₁ fun s₂ o₂ p₂ => ?_
  have O₂ := o₁.trans o₂
  refine wp_sig ssig0_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [O₂.gpr _ (by decide), hb]) (by rw [O₂.wr]; exact hA) h15 fun s₃ o₃ p₃ => ?_
  refine wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
    fun s₄ o₄ p₄ => ?_
  have O₄ := (O₂.trans o₃).trans o₄
  refine wp_add64m (by decide) (by decide) (by rw [O₄.gpr _ (by decide), hb]) (by rw [O₄.wr]; exact hA)
    h16 p₄ fun s₅ o₅ p₅ => ?_
  have O₅ := O₄.trans o₅
  refine wp_st (by rw [O₅.gpr _ (by decide), hb]) (by rw [O₅.wr]; exact hA) h16 p₅
    fun s₆ u₆ => k s₆ ?_
  rw [O₅.mem, o₁.mem, O₂.mem, O₄.mem, ← ssig1_eq, ← ssig0_eq] at u₆
  exact (O₅.mono (by decide)).wrote u₆

end

/-! ## A round -/

/-- `T₁` of a round. -/
def T1 (e f g h k w : BitVec 64) : BitVec 64 :=
  h + Spec.Sha512.bsig1 e + Spec.Sha512.ch e f g + k + w

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_roundW {a b c d e f g h w N : Nat} {k : BitVec 64} {B : BitVec 32}
    (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) (hc : c + 8 ≤ N) (hd : d + 8 ≤ N) (he : e + 8 ≤ N)
    (hf : f + 8 ≤ N) (hg : g + 8 ≤ N) (hh : h + 8 ≤ N) (hw : w + 8 ≤ N) (hfit : B.toNat + N ≤ 2 ^ 32)
    (hda : d + 8 ≤ a ∨ a + 8 ≤ d) (hdb : d + 8 ≤ b ∨ b + 8 ≤ d) (hdc : d + 8 ≤ c ∨ c + 8 ≤ d)
    (hA : Acc s.wr B N) (h0 : s.gpr .esi = B)
    (K : ∀ s', Wrote [Y0, Y1, Z0, Z1, T] s s'
      (write64 (write64 s.mem B d (rd64 s.mem B d +
          T1 (rd64 s.mem B e) (rd64 s.mem B f) (rd64 s.mem B g) (rd64 s.mem B h) k (rd64 s.mem B w)))
        B h
        (T1 (rd64 s.mem B e) (rd64 s.mem B f) (rd64 s.mem B g) (rd64 s.mem B h) k (rd64 s.mem B w) +
          (Spec.Sha512.bsig0 (rd64 s.mem B a) +
            Spec.Sha512.maj (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c)))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (roundW a b c d e f g h k w ++ rest)) s Q := by
  unfold roundW
  simp only [List.append_assoc]
  -- T₁
  refine wp_sig bsig1_ok (by decide) (by decide) (by decide) (by decide) (by decide) h0 hA he
    fun s₁ o₁ p₁ => ?_
  refine wp_ld (by decide) (by decide) (by rw [o₁.gpr _ (by decide), h0]) (by rw [o₁.wr]; exact hA) hh
    fun s₂ o₂ p₂ => ?_
  refine wp_add64 (by decide) (by decide) p₂ (p₁.of_only o₂ (by decide) (by decide))
    fun s₃ o₃ p₃ => ?_
  have O₃ := (o₁.trans o₂).trans o₃
  refine wp_ch (by rw [O₃.gpr _ (by decide), h0]) (by rw [O₃.wr]; exact hA) he hf hg fun s₄ o₄ p₄ => ?_
  refine wp_add64 (by decide) (by decide) (p₃.of_only o₄ (by decide) (by decide)) p₄
    fun s₅ o₅ p₅ => ?_
  refine wp_add64i (by decide) p₅ k fun s₆ o₆ p₆ => ?_
  have O₆ := ((O₃.trans o₄).trans o₅).trans o₆
  refine wp_add64m (by decide) (by decide) (by rw [O₆.gpr _ (by decide), h0]) (by rw [O₆.wr]; exact hA)
    hw p₆ fun s₇ o₇ p₇ => ?_
  have O₇ := O₆.trans o₇
  -- e' = d + T₁
  refine wp_ld (by decide) (by decide) (by rw [O₇.gpr _ (by decide), h0]) (by rw [O₇.wr]; exact hA) hd
    fun s₈ o₈ p₈ => ?_
  refine wp_add64 (by decide) (by decide) p₈ (p₇.of_only o₈ (by decide) (by decide))
    fun s₉ o₉ p₉ => ?_
  have O₉ := (O₇.trans o₈).trans o₉
  have p₇' := (p₇.of_only o₈ (by decide) (by decide)).of_only o₉ (by decide) (by decide)
  refine wp_st (by rw [O₉.gpr _ (by decide), h0]) (by rw [O₉.wr]; exact hA) hd p₉ fun s₁₀ u₁₀ => ?_
  have hA₁₀ : Acc s₁₀.wr B N := by rw [u₁₀.wr, O₉.wr]; exact hA
  have h0₁₀ : s₁₀.gpr .esi = B := by rw [u₁₀.gpr, O₉.gpr _ (by decide), h0]
  have p₇'' : Pair s₁₀ Y0 Y1 _ := ⟨by rw [u₁₀.gpr]; exact p₇'.1, by rw [u₁₀.gpr]; exact p₇'.2⟩
  -- a' = T₁ + Σ₀(a) + Maj(a, b, c)
  refine wp_sig bsig0_ok (by decide) (by decide) (by decide) (by decide) (by decide) h0₁₀ hA₁₀ ha
    fun s₁₁ o₁₁ p₁₁ => ?_
  refine wp_add64 (by decide) (by decide) (p₇''.of_only o₁₁ (by decide) (by decide)) p₁₁
    fun s₁₂ o₁₂ p₁₂ => ?_
  have O₁₂ := o₁₁.trans o₁₂
  refine wp_maj (by rw [O₁₂.gpr _ (by decide), h0₁₀]) (by rw [O₁₂.wr]; exact hA₁₀) ha hb hc
    fun s₁₃ o₁₃ p₁₃ => ?_
  refine wp_add64 (by decide) (by decide) (p₁₂.of_only o₁₃ (by decide) (by decide)) p₁₃
    fun s₁₄ o₁₄ p₁₄ => ?_
  have O₁₄ := (O₁₂.trans o₁₃).trans o₁₄
  refine wp_st (by rw [O₁₄.gpr _ (by decide), h0₁₀]) (by rw [O₁₄.wr]; exact hA₁₀) hh p₁₄
    fun s₁₅ u₁₅ => K s₁₅ ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₁₅.gpr, (O₁₄.mono (es := [Y0, Y1, Z0, Z1, T]) (by decide)).gpr r hr, u₁₀.gpr,
      (O₉.mono (es := [Y0, Y1, Z0, Z1, T]) (by decide)).gpr r hr]
  · have m₁₀ : s₁₀.mem = write64 s.mem B d (rd64 s.mem B d +
        T1 (rd64 s.mem B e) (rd64 s.mem B f) (rd64 s.mem B g) (rd64 s.mem B h) k (rd64 s.mem B w)) := by
      rw [u₁₀.mem, O₉.mem, O₇.mem, O₆.mem, O₃.mem, o₁.mem]
      simp only [T1, bsig1_eq]
    have r : ∀ x, x + 8 ≤ N → (d + 8 ≤ x ∨ x + 8 ≤ d) → rd64 s₁₀.mem B x = rd64 s.mem B x :=
      fun x hx hs => by rw [m₁₀]; exact rd64_write64_ne _ _ (by omega) (by omega) hs
    rw [u₁₅.mem, O₁₄.mem, O₁₂.mem, r a ha hda, r b hb hdb, r c hc hdc, m₁₀, o₁.mem, O₃.mem, O₆.mem]
    simp only [T1, bsig0_eq, bsig1_eq, BitVec.add_assoc]
  · rw [u₁₅.rd, O₁₄.rd, u₁₀.rd, O₉.rd]
  · rw [u₁₅.wr, O₁₄.wr, u₁₀.wr, O₉.wr]

end

end VG.Proof.Sha512.X86
