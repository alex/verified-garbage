import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# X448 on x86 (32-bit): instruction rules

Single-step rules expose register and memory updates while keeping the rest of
each state folded.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

structure Upd (s t : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : t.gpr d = v
  other : ∀ r, r ≠ d → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (v : BitVec 32) (cf of zf sf : Option Bool) :
    Upd s ((s.setFlags cf of zf sf).setReg d v) d v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem Upd.rest {s t : State} {d : Reg} {v : BitVec 32} (h : Upd s t d v) {rs : List Reg}
    (hd : d ∈ rs) : Keeps rs s t :=
  ⟨fun r hr => h.other r (fun e => hr (e ▸ hd)), h.rd, h.wr⟩

structure Mupd (s t : State) (m : Mem) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = m
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Mupd.rest {s t : State} {m : Mem} (h : Mupd s t m) (rs : List Reg) : Keeps rs s t :=
  ⟨fun r _ => congrFun h.gpr r, h.rd, h.wr⟩

structure Fupd (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Fupd.rest {s t : State} (h : Fupd s t) (rs : List Reg) : Keeps rs s t :=
  ⟨fun r _ => congrFun h.gpr r, h.rd, h.wr⟩

theorem Scr.of_upd {s t : State} {base : Addr} {d : Reg} {v : BitVec 32}
    (hs : Scr s base) (h : Upd s t d v) (hd : .edi ≠ d) : Scr t base :=
  ⟨by rw [h.other _ hd]; exact hs.edi, h.wr ▸ hs.wr,
    by rw [h.other _ hd]; exact hs.nowrap⟩

theorem WP.cons {i : Instr} {is : List Instr} {s t : State} {Q : State → Prop}
    (h : exec i s = some t) (k : WP isa (.block is) t Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨t, h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d v → WP isa (.block is) t Q) : WP isa (.block (.mov d src :: is)) s Q :=
  WP.cons (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _))

/-- The ALU operations that write their result and do not read carry. -/
def plain (op : AluOp) : Prop := op = .add ∨ op = .sub ∨ op = .and ∨ op = .or ∨ op = .xor

def aluVal (op : AluOp) (a b : BitVec 32) : BitVec 32 := match op with
  | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b | _ => 0

theorem wp_alu {op : AluOp} {d : Reg} {src : Src} {v : BitVec 32} (hop : plain op)
    (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (aluVal op (s.gpr d) v) →
      t.zf = some (aluVal op (s.gpr d) v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu op d src :: is)) s Q := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    refine WP.cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _ _) rfl)

theorem wp_shift {op : ShiftOp} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, Upd s t d (match op with | .shr => s.gpr d >>> n | .ror => (s.gpr d).rotateRight n) →
      WP isa (.block is) t Q) : WP isa (.block (.shift op d n :: is)) s Q := by
  cases op <;> refine WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _ _))

theorem wp_load {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hr : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ t, Upd s t d (s.mem.readW a 32) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q :=
  wp_mov (by simp only [readSrc, ha, State.load32, hr, ite_true]) k

theorem wp_store {r : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 4)
    (k : ∀ t, Mupd s t (s.mem.writeW a (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  WP.cons (t := {s with mem := s.mem.writeW a (s.gpr r)}) (by simp only [exec, ha, State.store32, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl⟩)

theorem wp_load8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  WP.cons (by simp only [exec, ha, State.load8, hr, ite_true, Option.map_some])
    (k _ (Upd.setReg _ _ _))

theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  WP.cons (t := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)}) (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl⟩)


theorem load_ok {base : Addr} (hs : Scr s base) {d : Reg} {o : Nat} (ho : o + 4 ≤ 8192)
    (k : ∀ t, Upd s t d (word s.mem base o) → WP isa (.block is) t Q) :
    WP isa (.block (ld d o :: is)) s Q :=
  wp_load (hs.ea (by omega)) (hs.read ho) k

theorem store_ok {base : Addr} (hs : Scr s base) {r : Reg} {o : Nat} (ho : o + 4 ≤ 8192)
    (k : ∀ t, Mupd s t (s.mem.writeW (off base o) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (st r o :: is)) s Q :=
  wp_store (hs.ea (by omega)) (hs.write ho) k


theorem wp_mul {r : Reg}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      t.mem = s.mem → Keeps [.eax, .edx] s t → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q := by
  refine WP.cons (t := execMul r s) rfl (k _ ?_ rfl ⟨?_, rfl, rfl⟩)
  · simp only [execMul, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]


theorem wp_cmp {r : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.zf = some (s.gpr r - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp r src :: is)) s Q :=
  WP.cons (t := arithFlags s (s.gpr r - v) ((s.gpr r).toNat < v.toNat)
    (subOverflow (s.gpr r) v (s.gpr r - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

end

end VG.Proof.X448.X86
