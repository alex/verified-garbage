import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Sha3.AArch64
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.Sha3.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Offset

section

section

/-!
# SHA-3 on AArch64: one instruction at a time

Weakest-precondition rules for the instruction forms the SHA-3 code uses,
exposing only what changes, so that proofs about a block stay small.
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vec : s'.v = s.v

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.vec.trans h₁.vec⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vec : s'.v = s.v

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Sha3.AArch64.mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_orr {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n ||| s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_ror {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).rotateRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.ror .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d ((s.gpr n).rotateRight sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

end

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

end VG.Proof.Sha3.AArch64

end

/-!
# Keccak-f[1600] on AArch64: one round

One round (`round`) from the state at `x0` to the state at `x1`, lane by lane
(`Proof.Sha3.out`), and the swap of `x0` and `x1` after it. The same structure
as the x86-64 proof (`VG.Proof.Sha3.X86_64`).
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3 (C D B out)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## Registers -/

/-- The pointers, which a round only moves between each other. -/
def ptrRegs : List Reg := [.x0, .x1, .x2, .x3]

theorem creg_inj : ∀ x < 5, ∀ x' < 5, creg x = creg x' → x = x' := by decide
theorem dreg_inj : ∀ x < 5, ∀ x' < 5, dreg x = dreg x' → x = x' := by decide
theorem creg_dreg : ∀ x < 5, ∀ x' < 5, creg x ≠ dreg x' := by decide
theorem creg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, creg x ≠ r := by decide
theorem dreg_ptr : ∀ x < 5, ∀ r ∈ ptrRegs, dreg x ≠ r := by decide
theorem T_ptr : ∀ r ∈ ptrRegs, T ≠ r := by decide
theorem R_ptr : ∀ r ∈ ptrRegs, R ≠ r := by decide
theorem T_creg : ∀ x < 5, T ≠ creg x := by decide
theorem T_dreg : ∀ x < 5, T ≠ dreg x := by decide
theorem R_creg : ∀ x < 5, R ≠ creg x := by decide
theorem R_dreg : ∀ x < 5, R ≠ dreg x := by decide
theorem R_T : R ≠ T := by decide

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : creg x' ≠ creg x :=
  fun e => h (creg_inj x' hx' x hx e)

theorem dreg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : dreg x' ≠ dreg x :=
  fun e => h (dreg_inj x' hx' x hx e)

/-! ## Addresses -/

theorem lane_off {i : Nat} (hi : i < 25) : 8 * i % 8 = 0 ∧ 8 * i < 4096 * 8 := ⟨by omega, by omega⟩

/-! ## What a phase changes -/

/-- `s'` is `s` with at most the registers `d` and `e` changed. -/
structure Chg (s s' : State) (d e : Reg) : Prop where
  other : ∀ r, r ≠ d → r ≠ e → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vec : s'.v = s.v

/-- What a phase of the round keeps. -/
structure Keeps (s s' : State) : Prop where
  ptrs : ∀ r ∈ ptrRegs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.ptrs r hr).trans (h₁.ptrs r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Keeps.ofUpd {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v)
    (hd : ∀ r ∈ ptrRegs, d ≠ r) : Keeps s s' :=
  ⟨fun r hr => h.other r (hd r hr).symm, h.rd, h.wr, h.sp⟩

theorem Keeps.ofChg {s s' : State} {d e : Reg} (h : Chg s s' d e)
    (hd : ∀ r ∈ ptrRegs, d ≠ r) (he : ∀ r ∈ ptrRegs, e ≠ r) : Keeps s s' :=
  ⟨fun r hr => h.other r (hd r hr).symm (he r hr).symm, h.rd, h.wr, h.sp⟩

/-! ## θ -/

/-- `ldr T, [x0, #8k]; eor c, c, T`. -/
theorem ldx_ok {c : Reg} (hc : c ≠ T) {k : Nat} (hk : k < 25) {s : State} {src : Addr}
    {rest : List Instr} {Q : State → Prop} (h0 : s.gpr .x0 = src)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr src k) 8)
    (cont : ∀ s', Chg s s' c T → s'.gpr c = s.gpr c ^^^ s.mem.readW (laneAddr src k) 64 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr .x T .x0 (8 * k) :: .logic .eor .x c c T :: rest)) s Q := by
  refine wp_ldr (lane_off hk) (by rw [h0]) hin fun s₁ u₁ => wp_eor fun s₂ u₂ => cont s₂ ?_ ?_
  · exact ⟨fun r h h' => by rw [u₂.other r h, u₁.other r h'], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp], by rw [u₂.vec, u₁.vec]⟩
  · rw [u₂.gpr, u₁.other _ hc, u₁.gpr]

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (src : Addr) (A : KState)
    (hx0 : s.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : Lanes s.mem src A) :
    WP isa (.block (column x)) s fun s' => s'.gpr (creg x) = C A x ∧ Chg s s' (creg x) T := by
  have hc : creg x ≠ T := (T_creg x hx).symm
  have c0 : creg x ≠ .x0 := creg_ptr x hx .x0 (by decide)
  have T0 : T ≠ .x0 := T_ptr .x0 (by decide)
  have hv : ∀ k (hk : k < 25), s.mem.readW (laneAddr src k) 64 = A[k]! := fun k hk => by
    rw [hA k hk]; simp [hk]
  unfold column
  refine wp_ldr (lane_off (by omega : x < 25)) (by rw [hx0]) (hin x (by omega)) fun s₁ u₁ => ?_
  have e₁ : ∀ t : State, Chg s₁ t (creg x) T → Chg s t (creg x) T ∧ t.gpr .x0 = src ∧
      InRegions (t.rd ++ t.wr) = InRegions (s.rd ++ s.wr) ∧ t.mem = s.mem := fun t h =>
    ⟨⟨fun r h' h'' => by rw [h.other r h' h'', u₁.other r h'], by rw [h.mem, u₁.mem],
      by rw [h.rd, u₁.rd], by rw [h.wr, u₁.wr], by rw [h.sp, u₁.sp], by rw [h.vec, u₁.vec]⟩,
      by rw [h.other _ (Ne.symm c0) (Ne.symm T0), u₁.other _ (Ne.symm c0), hx0],
      by rw [h.rd, h.wr, u₁.rd, u₁.wr], by rw [h.mem, u₁.mem]⟩
  have c₁ : Chg s₁ s₁ (creg x) T := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, a₁, i₁, m₁⟩ := e₁ s₁ c₁
  refine ldx_ok hc (k := x + 5) (by omega) a₁ (by rw [i₁]; exact hin _ (by omega)) fun s₂ h₂ v₂ => ?_
  have c₂ : Chg s₁ s₂ (creg x) T := h₂
  obtain ⟨-, a₂, i₂, m₂⟩ := e₁ s₂ c₂
  refine ldx_ok hc (k := x + 10) (by omega) a₂ (by rw [i₂]; exact hin _ (by omega)) fun s₃ h₃ v₃ => ?_
  have c₃ : Chg s₁ s₃ (creg x) T :=
    ⟨fun r h h' => by rw [h₃.other r h h', h₂.other r h h'], by rw [h₃.mem, h₂.mem],
      by rw [h₃.rd, h₂.rd], by rw [h₃.wr, h₂.wr], by rw [h₃.sp, h₂.sp], by rw [h₃.vec, h₂.vec]⟩
  obtain ⟨-, a₃, i₃, m₃⟩ := e₁ s₃ c₃
  refine ldx_ok hc (k := x + 15) (by omega) a₃ (by rw [i₃]; exact hin _ (by omega)) fun s₄ h₄ v₄ => ?_
  have c₄ : Chg s₁ s₄ (creg x) T :=
    ⟨fun r h h' => by rw [h₄.other r h h', c₃.other r h h'], by rw [h₄.mem, c₃.mem],
      by rw [h₄.rd, c₃.rd], by rw [h₄.wr, c₃.wr], by rw [h₄.sp, c₃.sp], by rw [h₄.vec, c₃.vec]⟩
  obtain ⟨-, a₄, i₄, m₄⟩ := e₁ s₄ c₄
  refine ldx_ok hc (k := x + 20) (by omega) a₄ (by rw [i₄]; exact hin _ (by omega)) fun s₅ h₅ v₅ => wp_nil ?_
  have c₅ : Chg s₁ s₅ (creg x) T :=
    ⟨fun r h h' => by rw [h₅.other r h h', c₄.other r h h'], by rw [h₅.mem, c₄.mem],
      by rw [h₅.rd, c₄.rd], by rw [h₅.wr, c₄.wr], by rw [h₅.sp, c₄.sp], by rw [h₅.vec, c₄.vec]⟩
  refine ⟨?_, (e₁ s₅ c₅).1⟩
  rw [v₅, v₄, v₃, v₂, u₁.gpr]
  simp only [m₄, m₃, m₂, m₁]
  rw [hv x (by omega), hv _ (by omega),
    hv _ (by omega), hv _ (by omega), hv _ (by omega)]
  rfl

/-- After the first `k` columns. -/
def ColInv (s₀ : State) (A : KState) (k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ ∀ x < k, s.gpr (creg x) = C A x

theorem columns_ok (s₀ : State) (src : Addr) (A : KState)
    (hx0 : s₀.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : Lanes s₀.mem src A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hk, hm, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Keeps.refl _, rfl, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx s src A ((hk.ptrs .x0 (by decide)).trans hx0)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA)) fun s' ⟨hv, h⟩ => ?_
  refine ⟨hk.trans (Keeps.ofChg h (creg_ptr x hx) T_ptr), h.mem.trans hm, fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact hv
  · rw [h.other _ (creg_ne hx (by omega) e) (T_creg x' (by omega)).symm, hc x' (by omega)]

/-! ## D -/

theorem dcol_ok (x : Nat) (hx : x < 5) (s : State) (A : KState)
    (hc : ∀ x' < 5, s.gpr (creg x') = C A x') :
    WP isa (.block (dcol x)) s fun s' => Upd s s' (dreg x) (D A x) := by
  unfold dcol
  refine wp_ror (by decide) fun s₁ h₁ => wp_eor fun s₂ h₂ => wp_nil ?_
  have u := h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp, h₂.vec⟩
  refine ⟨?_, u.other, u.mem, u.rd, u.wr, u.sp, u.vec⟩
  rw [h₂.gpr, h₁.gpr, h₁.other _ (creg_dreg _ (Nat.mod_lt _ (by omega)) x hx),
    hc _ (Nat.mod_lt _ (by omega)), hc _ (Nat.mod_lt _ (by omega))]
  rfl

/-- After the first `k` of the `D[x]`. -/
def DInv (s₀ : State) (A : KState) (k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ (∀ x < 5, s.gpr (creg x) = C A x) ∧ ∀ x < k, s.gpr (dreg x) = D A x

theorem dcols_ok (s₀ : State) (A : KState) (hc : ∀ x < 5, s₀.gpr (creg x) = C A x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ A) (fun x s hx ⟨hk, hm, hcs, hd⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Keeps.refl _, rfl, hc, fun _ h => absurd h (by omega)⟩
  refine WP.mono (dcol_ok x hx s A hcs) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (dreg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [h.other _ (creg_dreg x' hx' x hx), hcs x' hx']
  · by_cases e : x' = x
    · subst e; exact h.gpr
    · rw [h.other _ (dreg_ne hx (by omega) e), hd x' (by omega)]

/-! ## A plane -/

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) (s : State) (src : Addr) (A : KState)
    (hx0 : s.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x' < 5, s.gpr (dreg x') = D A x') :
    WP isa (.block (laneB x y)) s fun s' => Upd s s' (creg x) (B A x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold laneB
  rw [List.cons_append, List.cons_append]
  refine wp_ldr (lane_off hj) (by rw [hx0]) (hin _ hj) fun s₁ h₁ => wp_eor fun s₂ h₂ => ?_
  have u := h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp, h₂.vec⟩
  have hv : s₂.gpr (creg x) = A[piSrc x y]! ^^^ D A ((x + 3 * y) % 5) := by
    rw [h₂.gpr, h₁.gpr, hA _ hj, h₁.other _ (creg_dreg x hx _ hk).symm, hd _ hk]
  unfold B Proof.Sha3.rotl
  split
  · exact wp_nil ⟨by rw [hv], u.other, u.mem, u.rd, u.wr, u.sp, u.vec⟩
  · have := Proof.Sha3.rhoOff_lt _ hj
    refine wp_ror (by omega) fun s₃ h₃ => wp_nil ?_
    refine ⟨by rw [h₃.gpr, hv], (u.trans ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr, h₃.sp, h₃.vec⟩).other,
      by rw [h₃.mem, u.mem], by rw [h₃.rd, u.rd], by rw [h₃.wr, u.wr], by rw [h₃.sp, u.sp], by rw [h₃.vec, u.vec]⟩

/-- After the first `k` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (A : KState) (y k : Nat) (s : State) : Prop :=
  Keeps s₀ s ∧ s.mem = s₀.mem ∧ (∀ x < 5, s.gpr (dreg x) = D A x) ∧
    ∀ x < k, s.gpr (creg x) = B A x y

theorem laneBs_ok (y : Nat) (_hy : y < 5) (s₀ : State) (src : Addr) (A : KState)
    (hx0 : s₀.gpr .x0 = src) (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr src i) 8)
    (hA : ∀ i < 25, s₀.mem.readW (laneAddr src i) 64 = A[i]!)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB x y)) s₀ (BInv s₀ A y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ A y) (fun x s hx ⟨hk, hm, hds, hb⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Keeps.refl _, rfl, hd, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx _hy s src A ((hk.ptrs .x0 (by decide)).trans hx0)
    (by rw [hk.rd, hk.wr]; exact hin) (by rw [hm]; exact hA) hds) fun s' h => ?_
  refine ⟨hk.trans (Keeps.ofUpd h (creg_ptr x hx)), h.mem.trans hm, fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [h.other _ (creg_dreg x hx x' hx').symm, hds x' hx']
  · by_cases e : x' = x
    · subst e; exact h.gpr
    · rw [h.other _ (creg_ne hx (by omega) e), hb x' (by omega)]

/-- `¬b ∧ c`, as the model computes it without `bic`. -/
theorem andNot (b c : Lane) : (b ^^^ 0xffffffffffffffff) &&& c = (b &&& c) ^^^ c := by
  have e : (0xffffffffffffffff : Lane) = BitVec.allOnes 64 := by decide
  rw [e]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_allOnes]
  cases b[i] <;> cases c[i] <;> rfl

/-- What `chi` leaves: `T` and `R` changed, and lane `(x, y)` of the output
stored. -/
structure ChiPost (s s' : State) (a : Addr) (v : Lane) : Prop where
  other : ∀ r, r ≠ T → r ≠ R → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem.writeW a v

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) (s : State) (dst rcp : Addr) (A : KState)
    (rc : Lane) (hx1 : s.gpr .x1 = dst) (hx2 : s.gpr .x2 = rcp)
    (hout : InRegions s.wr (laneAddr dst (x + 5 * y)) 8) (hrc_in : InRegions (s.rd ++ s.wr) rcp 8)
    (hrc : s.mem.readW rcp 64 = rc) (hb : ∀ x' < 5, s.gpr (creg x') = B A x' y) :
    WP isa (.block (chi x y)) s fun s' => ChiPost s s' (laneAddr dst (x + 5 * y)) (out A rc x y) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have hj : x + 5 * y < 25 := by omega
  unfold chi
  simp only [List.cons_append]
  refine wp_and fun s₁ h₁ => wp_eor fun s₂ h₂ => wp_eor fun s₃ h₃ => ?_
  have u := (h₁.trans ⟨h₂.gpr, h₂.other, h₂.mem, h₂.rd, h₂.wr, h₂.sp, h₂.vec⟩).trans
    ⟨h₃.gpr, h₃.other, h₃.mem, h₃.rd, h₃.wr, h₃.sp, h₃.vec⟩
  have ht : s₃.gpr T = (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^
      B A x y := by
    rw [h₃.gpr, h₂.gpr, h₁.gpr, h₂.other _ (T_creg _ hx).symm, h₁.other _ (T_creg _ hx).symm,
      h₁.other _ (T_creg _ h2).symm, hb _ h1, hb _ h2, hb _ hx, andNot]
  have fin : ∀ s₄ : State, (∀ r, r ≠ T → r ≠ R → s₄.gpr r = s.gpr r) → s₄.gpr T = out A rc x y →
      s₄.mem = s.mem → s₄.rd = s.rd → s₄.wr = s.wr → s₄.sp = s.sp →
      WP isa (.block [.str .x T .x1 (8 * (x + 5 * y))]) s₄ fun s' =>
        ChiPost s s' (laneAddr dst (x + 5 * y)) (out A rc x y) := fun s₄ g₄ v₄ m₄ r₄ w₄ p₄ => by
    refine wp_str (lane_off hj) (by rw [g₄ _ (T_ptr .x1 (by decide)).symm (R_ptr .x1 (by decide)).symm, hx1])
      (by rw [w₄]; exact hout) fun s₅ g₅ => wp_nil ?_
    exact ⟨fun r h h' => by rw [g₅.gpr, g₄ r h h'], by rw [g₅.rd, r₄], by rw [g₅.wr, w₄],
      by rw [g₅.sp, p₄], by rw [g₅.mem, m₄, v₄]⟩
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [and_self, ite_true, List.cons_append, List.nil_append]
    refine wp_ldr (a := rcp) ⟨by decide, by decide⟩
      (by rw [u.other _ (T_ptr .x2 (by decide)).symm, hx2]; exact add_zero' _)
      (by rw [u.rd, u.wr]; exact hrc_in) fun s₄ h₄ => wp_eor fun s₅ h₅ => ?_
    refine fin s₅ (fun r h h' => by rw [h₅.other r h, h₄.other r h', u.other r h]) ?_
      (by rw [h₅.mem, h₄.mem, u.mem]) (by rw [h₅.rd, h₄.rd, u.rd]) (by rw [h₅.wr, h₄.wr, u.wr])
      (by rw [h₅.sp, h₄.sp, u.sp])
    rw [h₅.gpr, h₄.other _ (Ne.symm R_T), h₄.gpr, ht, u.mem, hrc, out]
    simp only [and_self, ite_true]
  · simp only [h0, ite_false, List.nil_append]
    refine fin s₃ (fun r h _ => u.other r h) ?_ u.mem u.rd u.wr u.sp
    rw [ht, out]
    simp only [h0, ite_false]

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (A : KState) (rc : Lane) (dst : Addr) (y k : Nat) (s : State) : Prop where
  keeps : Keeps s₀ s
  frame : Frame [⟨dst, 200⟩] s₀.mem s.mem
  dregs : ∀ x < 5, s.gpr (dreg x) = D A x
  bregs : ∀ x < 5, s.gpr (creg x) = B A x y
  lanes : ∀ j < 5 * y + k, s.mem.readW (laneAddr dst j) 64 = out A rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) (s₀ : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hx1 : s₀.gpr .x1 = dst) (hx2 : s₀.gpr .x2 = rcp)
    (hrc : s₀.mem.readW rcp 64 = rc) (s : State) (hs : ChiInv s₀ A rc dst y 0 s) :
    WP isa (.block ((List.range 5).flatMap fun x => chi x y)) s (ChiInv s₀ A rc dst y 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A rc dst y) (fun x s hx hi => ?_) 5 (Nat.le_refl _) s hs
  have hj : x + 5 * y < 25 := by omega
  refine WP.mono (chi_ok x y hx hy s dst rcp A rc ((hi.keeps.ptrs .x1 (by decide)).trans hx1)
    ((hi.keeps.ptrs .x2 (by decide)).trans hx2) (by rw [hi.keeps.wr]; exact he.dst_out _ hj)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.rc_in) (by rw [he.rc_frame hi.frame, hrc]) hi.bregs)
    fun s' hc => ?_
  refine ⟨⟨fun r hr => by rw [hc.other r (T_ptr r hr).symm (R_ptr r hr).symm, hi.keeps.ptrs r hr],
      hc.rd.trans hi.keeps.rd, hc.wr.trans hi.keeps.wr, hc.sp.trans hi.keeps.sp⟩, ?_,
    fun x' hx' => by rw [hc.other _ (T_dreg x' hx').symm (R_dreg x' hx').symm, hi.dregs x' hx'],
    fun x' hx' => by rw [hc.other _ (T_creg x' hx').symm (R_creg x' hx').symm, hi.bregs x' hx'],
    fun j hj' => ?_⟩
  · rw [hc.mem]; exact hi.frame.writeW (List.mem_singleton_self _) _ (lane_contains dst hj)
  · rw [hc.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [Mem.readW_writeW_self64, show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]
    · rw [Mem.readW_writeW_sep (lane_sep dst (by omega) hj e) (by decide)]
      exact hi.lanes j (by omega)

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (A : KState) (rc : Lane) (dst : Addr) (y : Nat) (s : State) : Prop where
  keeps : Keeps s₀ s
  frame : Frame [⟨dst, 200⟩] s₀.mem s.mem
  dregs : ∀ x < 5, s.gpr (dreg x) = D A x
  lanes : ∀ j < 5 * y, s.mem.readW (laneAddr dst j) 64 = out A rc (j % 5) (j / 5)

theorem planes_ok (s₀ : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s₀.rd s₀.wr src dst rcp) (hx0 : s₀.gpr .x0 = src) (hx1 : s₀.gpr .x1 = dst)
    (hx2 : s₀.gpr .x2 = rcp) (hA : Lanes s₀.mem src A) (hrc : s₀.mem.readW rcp 64 = rc)
    (hd : ∀ x < 5, s₀.gpr (dreg x) = D A x) :
    WP isa (.block ((List.range 5).flatMap plane)) s₀ (PInv s₀ A rc dst 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ A rc dst) (fun y s hy hi => ?_) 5 (Nat.le_refl _) s₀
    ⟨Keeps.refl _, Frame.refl _ _, hd, fun _ h => absurd h (by omega)⟩
  unfold plane
  rw [WP.block_append_iff]
  have hA' : ∀ i < 25, s.mem.readW (laneAddr src i) 64 = A[i]! := fun i hi' => by
    rw [he.src_frame hi.frame hi', hA i hi']; simp [hi']
  refine WP.mono (laneBs_ok y hy s src A ((hi.keeps.ptrs .x0 (by decide)).trans hx0)
    (by rw [hi.keeps.rd, hi.keeps.wr]; exact he.src_in) hA' hi.dregs) fun s₁ ⟨hk, hm, hds, hb⟩ => ?_
  refine WP.mono (chis_ok y hy s₀ src dst rcp A rc he hx1 hx2 hrc s₁
    ⟨hi.keeps.trans hk, by rw [hm]; exact hi.frame, hds, hb, fun j hj => by rw [hm]; exact hi.lanes j hj⟩)
    fun s₂ h₂ => ⟨h₂.keeps, h₂.frame, h₂.dregs, fun j hj => h₂.lanes j (by omega)⟩

/-! ## The round -/

theorem tail_ok (s : State) :
    WP isa (.block [mov T .x0, mov .x0 .x1, mov .x1 T, .addImm .x .x2 .x2 8, .sub .x T .x2 .x3]) s
      fun s' =>
      s'.gpr .x0 = s.gpr .x1 ∧ s'.gpr .x1 = s.gpr .x0 ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧
      s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr T = s.gpr .x2 + BitVec.ofNat 64 8 - s.gpr .x3 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine wp_mov fun s₁ h₁ => wp_mov fun s₂ h₂ => wp_mov fun s₃ h₃ => wp_addImm (by decide)
    fun s₄ h₄ => wp_sub fun s₅ h₅ => wp_nil ?_
  have x2 : s₄.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 := by
    rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  have x3 : s₄.gpr .x3 = s.gpr .x3 := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  refine ⟨?_, ?_, by rw [h₅.other _ (by decide), x2], by rw [h₅.other _ (by decide), x3],
    by rw [h₅.gpr, x2, x3], by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr,
      h₁.other _ (by decide)]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.gpr]

theorem round_ok (s : State) (src dst rcp : Addr) (A : KState) (rc : Lane)
    (he : Env s.rd s.wr src dst rcp) (hx0 : s.gpr .x0 = src) (hx1 : s.gpr .x1 = dst)
    (hx2 : s.gpr .x2 = rcp) (hA : Lanes s.mem src A) (hrc : s.mem.readW rcp 64 = rc) :
    WP isa (.block round) s fun s' =>
      Lanes s'.mem dst (outState A rc) ∧ Frame [⟨dst, 200⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .x0 = dst ∧ s'.gpr .x1 = src ∧
      s'.gpr .x2 = rcp + BitVec.ofNat 64 8 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      s'.gpr T = rcp + BitVec.ofNat 64 8 - s.gpr .x3 := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s src A hx0 he.src_in hA) fun s₁ ⟨k₁, m₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A c₁) fun s₂ ⟨k₂, m₂, _, d₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  refine WP.mono (planes_ok s₂ src dst rcp A rc (by rw [k₁₂.rd, k₁₂.wr]; exact he)
    ((k₁₂.ptrs .x0 (by decide)).trans hx0) ((k₁₂.ptrs .x1 (by decide)).trans hx1)
    ((k₁₂.ptrs .x2 (by decide)).trans hx2) (by rw [m₂, m₁]; exact hA) (by rw [m₂, m₁, hrc]) d₂)
    fun s₃ h₃ => ?_
  have k₃ := k₁₂.trans h₃.keeps
  refine WP.mono (tail_ok s₃) fun s₄ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ => ?_
  have hdx : s₃.gpr .x2 = rcp := (k₃.ptrs .x2 (by decide)).trans hx2
  have hcx : s₃.gpr .x3 = s.gpr .x3 := k₃.ptrs .x3 (by decide)
  refine ⟨fun i hi => ?_, by rw [e₆, ← m₁, ← m₂]; exact h₃.frame, by rw [e₇, k₃.rd],
    by rw [e₈, k₃.wr], by rw [e₉, k₃.sp], by rw [e₁, k₃.ptrs .x1 (by decide), hx1],
    by rw [e₂, k₃.ptrs .x0 (by decide), hx0], by rw [e₃, hdx], by rw [e₄, hcx],
    by rw [e₅, hdx, hcx]⟩
  rw [e₆, h₃.lanes i (by omega)]
  simp [outState]

end VG.Proof.Sha3.AArch64

end

/-!
# Keccak-f[1600] on AArch64: the whole function

The same structure as the x86-64 proof (`VG.Proof.Sha3.X86_64`), with one
round per iteration: the AArch64 constant-time analysis tracks only which
registers are public, so swapping the pointers every round loses nothing.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.AArch64 in
/-- AArch64 contract for `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut
[u64; 64])`: applies Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap. The pointers
are public; the state is secret. -/
def permuteAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let scratch : Region := ⟨s.gpr .x1, 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .x0) = keccakF (stateAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_keccak_absorb(state = x0, rate = x1, pos = x2,
data = x3, len = x4, scratch = x5) -> x0`: absorbs `data` into the streaming
state (`Repr`) and returns the new position in the block.

The code may read `data`, and read and write `state` (200 bytes) and
`scratch` (640 bytes), none of which overlap each other or the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
`rate` is one of `rates`, and `pos < rate`. -/
def absorbAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat < (s.gpr .x1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .x0) (s.gpr .x1).toNat msg →
      (s.gpr .x2).toNat = msg.length % (s.gpr .x1).toNat →
      Repr s'.mem (s.gpr .x0) (s.gpr .x1).toNat
        (msg ++ bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ∧
    (s'.gpr .x0).toNat = ((s.gpr .x2).toNat + (s.gpr .x4).toNat) % (s.gpr .x1).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_keccak_pad(state = x0, rate = x1, pos = x2,
suffix = x3, scratch = x4)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
none of which overlap each other or the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. `rate` is one of
`rates`, and `pos < rate`. -/
def padAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let scratch : Region := ⟨s.gpr .x4, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat < (s.gpr .x1).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .x0) (s.gpr .x1).toNat msg →
    (s.gpr .x2).toNat = msg.length % (s.gpr .x1).toNat →
    stateAt s'.mem (s.gpr .x0) =
      absorb (s.gpr .x1).toNat (pad (s.gpr .x1).toNat ((s.gpr .x3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_keccak_squeeze(state = x0, rate = x1, pos = x2,
out = x3, outlen = x4, scratch = x5) -> x0`: writes `outlen` bytes of output
from byte `pos` on to `out`, and returns the position after them, leaving a
state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), none of which overlap each other or the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
`rate` is one of `rates`, and `pos ≤ rate`. -/
def squeezeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let out : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 640⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x2).toNat ≤ (s.gpr .x1).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
      squeezeFrom (s.gpr .x1).toNat (stateAt s.mem (s.gpr .x0)) (s.gpr .x2).toNat (s.gpr .x4).toNat ∧
    (s'.gpr .x0).toNat ≤ (s.gpr .x1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .x1).toNat (stateAt s'.mem (s.gpr .x0)) (s'.gpr .x0).toNat d =
      squeezeFrom (s.gpr .x1).toNat (stateAt s.mem (s.gpr .x0))
        ((s.gpr .x2).toNat + (s.gpr .x4).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

end VG.Proof.Sha3

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev scr : Addr := s₀.gpr .x1
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then st s₀ else scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then scr s₀ else st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem oth_succ (s₀ : State) (r : Nat) : oth s₀ (r + 1) = cur s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = st s₀ ∧ oth s₀ r = scr s₀) ∨ (cur s₀ r = scr s₀ ∧ oth s₀ r = st s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = stR s₀ ∨ R = scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega) (by omega))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (stR s₀).Disjoint ⟨scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega))
  · have := off_disjoint (scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega) (by omega)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (cur s₀ r) (oth s₀ r) (off s₀ (200 + 8 * r)) := by
  have hc := cur_cases s₀ r
  have hcur : cur s₀ r = st s₀ ∨ cur s₀ r = scr s₀ := hc.imp (·.1) (·.1)
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega)), ?_, h.region_off hoth (by omega) (by omega)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The round constants -/

/-- The round constants are in the scratch space. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, m.readW (off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 392 → Region.Disjoint ⟨off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    Aux s₀ m' := fun j hj => by
  rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
  exact h j hj

/-! ## The prologue -/

/-- `movz`, then three `movk`s, build round constant `k`, and the store puts it
in the scratch space. -/
theorem rcStore_ok (k : Nat) (hk : k < 24) (s : State)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (200 + 8 * k)) 8) :
    WP isa (.block (rcStore k)) s fun s' =>
      (∀ r, r ≠ R → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 (200 + 8 * k)) (RC k) := by
  have _ := hk
  unfold rcStore
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl
    (WP.cons (exec_str_x ⟨by omega, by omega⟩ ?_) (wp_nil ⟨?_, rfl, rfl, rfl, ?_⟩)))))
  · simpa [State.write, R] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true,
      show Reg.x1 ≠ R from by decide, ite_false]
    exact congrArg _ (movz_movk64' _)

/-- During the stores of the round constants. -/
def RcInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .x0 = st s₀ ∧ s.gpr .x1 = scr s₀ ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
    Frame [⟨off s₀ 200, 192⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ((List.range 24).flatMap rcStore)) s₀ (RcInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀) (fun k s hk ⟨hx0, hx1, hrd, hwr, hsp, hf, hv⟩ => ?_)
    24 (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (rcStore_ok k hk s
    (by rw [hwr, hx1]; exact hp.off_in (by omega))) fun s' ⟨g', r', w', p', m'⟩ => ?_
  rw [hx1] at m'
  refine ⟨by rw [g' _ (by decide), hx0], by rw [g' _ (by decide), hx1], r'.trans hrd, w'.trans hwr,
    p'.trans hsp, ?_, fun j hj => ?_⟩
  · rw [m']
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    have e : scr s₀ + BitVec.ofNat 64 (200 + 8 * k) = off s₀ 200 + BitVec.ofNat 64 (8 * k) := by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl
    rw [e]; exact contains_offset (by omega) (by omega)
  · rw [m']
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The rounds' invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = cur s₀ r
  x1 : s.gpr .x1 = oth s₀ r
  x2 : s.gpr .x2 = off s₀ (200 + 8 * r)
  x3 : s.gpr .x3 = off s₀ 392
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  unfold prologue
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp) fun s₁ ⟨di₁, si₁, rd₁, wr₁, sp₁, f₁, v₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ => wp_addImm (by decide) fun s₃ h₃ => wp_nil ?_
  have m : s₃.mem = s₁.mem := by rw [h₃.mem, h₂.mem]
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_offset (by omega) (by omega)⟩
  refine ⟨by rw [h₃.other _ (by decide), h₂.other _ (by decide), di₁]; simp [cur],
    by rw [h₃.other _ (by decide), h₂.other _ (by decide), si₁]; simp [oth], ?_, ?_,
    by rw [h₃.sp, h₂.sp, sp₁], by rw [h₃.rd, h₂.rd, rd₁], by rw [h₃.wr, h₂.wr, wr₁], ?_,
    fun j hj => by rw [m]; exact v₁ j hj, by rw [m]; exact hf₂⟩
  · rw [h₃.other _ (by decide), h₂.gpr, si₁]
  · rw [h₃.gpr, h₂.other _ (by decide), si₁]
  · intro i hi
    have hc : cur s₀ 0 = st s₀ := by simp [cur]
    rw [hc, m, f₁.readW (lane_contains _ hi)
      (by simpa using hp.region_off (.inl rfl) (d := 200) (n := 192) (by omega) (by omega)) (by decide)]
    simp [Spec.Sha3.stateAt, laneAddr]

/-! ## The rounds -/

theorem off_add8 (s₀ : State) (d : Nat) : off s₀ d + BitVec.ofNat 64 8 = off s₀ (d + 8) := by
  simp only [off]; rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem off_ne0 (s₀ : State) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (off s₀ a - off s₀ b != 0) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    intro e
    apply h
    simp only [off] at e
    bv_omega

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {s : State} (hL : LInv s₀ r s) :
    WP isa (.block round) s fun s' =>
      eval (.nonzero .x T) s' = some (!decide (r + 1 = 24)) ∧ LInv s₀ (r + 1) s' := by
  have he := hp.env r hr
  have hc := cur_cases s₀ r
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine WP.mono (round_ok s _ _ _ _ (RC r) (by rw [hL.rd, hL.wr]; exact he) hL.x0 hL.x1 hL.x2
    hL.state (hL.aux r hr)) fun s' ⟨hl, hf, hrd, hwr, hsp, h0, h1, h2, h3, hT⟩ => ?_
  have hL' : LInv s₀ (r + 1) s' := by
    refine ⟨by rw [h0, cur_succ], by rw [h1, oth_succ], by rw [h2, off_add8]; congr 1,
      by rw [h3, hL.x3], by rw [hsp, hL.sp], hrd.trans hL.rd, hwr.trans hL.wr, ?_, ?_, ?_⟩
    · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
    · exact hL.aux.frame (fun d hd hd' => (hp.region_off hoth hd (by omega)).symm) hf
    · refine hL.frame.trans (hf.sub fun R hR => ?_)
      simp only [List.mem_singleton] at hR; subst hR
      rcases hoth with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
  refine ⟨?_, hL'⟩
  rw [eval_nonzero, hT, hL.x3, off_add8, off_ne0 s₀ (by omega) (by omega)]
  simp only [show (200 + 8 * r + 8 = 392) = (r + 1 = 24) by apply propext; omega]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => s'.sp = s₀.sp ∧ Proof.Sha3.permuteAArch64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  let Inv : Nat → State → Prop := fun n s => ∃ r, n = 24 - r ∧ r < 24 ∧ LInv s₀ r s
  refine WP.loop (M := isa) Inv (fun n s ⟨r, hn, hr, hL⟩ => ?_) 24 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (round_step hp hr hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : r + 1 = 24
  · refine .inl ⟨by show VG.AArch64.eval (.nonzero .x T) s' = _; rw [he, hlast]; rfl, by rw [hl.sp], ?_⟩
    show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
    apply Vector.ext
    intro i hi
    have := hl.state i hi
    simp only [cur, hlast, show 24 % 2 = 0 from rfl, ite_true] at this
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn]
    exact this
  · exact .inr ⟨by show VG.AArch64.eval (.nonzero .x T) s' = _; rw [he]; simp [hlast], 24 - (r + 1), by omega, r + 1, rfl,
      by omega, hl⟩

/-- No instruction writes a callee-saved register. -/
theorem permute_preserved : ∀ r ∈ preserved, ∀ i ∈ instrs permute, dstOf i ≠ some r := by
  have : ((instrs permute).all fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem permute_noCalls : permute.noCalls = true := by decide +kernel

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.AArch64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteAArch64.post s s' := by
  obtain ⟨t, s', he, hsp, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he,
    ⟨fun r hr => Exec.gpr (permute_preserved r hr) he (.inl permute_noCalls), hsp, Exec.preservedV he⟩, h⟩

theorem permute_ct : ConstantTime isa Proof.Sha3.permuteAArch64.pre Proof.Sha3.permuteAArch64.pub
    Impl.Sha3.AArch64.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem permute_verified :
    Verified AArch64.target Impl.Sha3.AArch64.permute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct permute_correct permute_ct (by
    sig_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Sha3.AArch64.satState] using Proof.Sha3.AArch64.satState)

theorem permute_noFrames : permute.noFrames = true := by decide +kernel

end VG.Proof.Sha3.AArch64
