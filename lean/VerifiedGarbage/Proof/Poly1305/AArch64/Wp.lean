import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Poly1305 on AArch64: one instruction at a time

Untrusted: everything here is checked by Lean. Weakest-precondition rules
for the instruction forms of the byte loops and the counts of `update` and
`finalize`, exposing only what changes.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

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
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

end

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [VG.AArch64.eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [VG.AArch64.eval, State.read]

end VG.Proof.Poly1305.AArch64
