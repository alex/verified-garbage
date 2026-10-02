import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: single instructions

Untrusted: everything here is checked by Lean. Each instruction the
functions run, as a step of a block that leaves its result and changes
nothing else (`Only` the register it writes, or `MemTo` the memory a store
leaves), passed on to the rest of the block.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm

/-- `s'` differs from `s` only in the registers `rs` (and the flags). -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Only

theorem refl (rs : List Reg) (s : State) : Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only rs s₁ s₂) (h₂ : Only rs s₂ s₃) : Only rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

theorem get {rs : List Reg} {s s' : State} (h : Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Only

/-- `s'` is `s` with the memory `m`. -/
structure MemTo (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

theorem only_setReg (s : State) (d : Reg) (x : BitVec 32) : Only [d] s (s.setReg d x) :=
  ⟨fun r hr => by
    simp only [List.mem_singleton] at hr
    simp [State.setReg, hr], rfl, rfl, rfl, rfl⟩

/-- An instruction that writes the register `d`. -/
theorem wp_setReg {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {x : BitVec 32}
    (he : exec i s = some (s.setReg d x))
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = x → WP isa (.block is) s1 Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, he, k _ (only_setReg s d x) (by simp [State.setReg])⟩

theorem wp_ldr {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldr t n off :: is)) s Q :=
  wp_setReg (exec_ldr ho h) k

theorem wp_ldrSp {t : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, Only [t] s s1 → s1.gpr t = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      WP isa (.block is) s1 Q) : WP isa (.block (.ldrSp t off :: is)) s Q :=
  wp_setReg (by simp only [exec, ho, ite_true, State.load32, h, Option.map_some]) k

theorem wp_movw {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = v.setWidth 32 → WP isa (.block is) s1 Q) :
    WP isa (.block (.movw d v :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movt {d : Reg} {v : BitVec 16} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = (v ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s1 Q) :
    WP isa (.block (.movt d v :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movReg {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr r → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_setReg rfl k

theorem wp_movImm {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, Only [d] s s1 → s1.gpr d = v → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_movLsr {d r : Reg} {n : Nat} {is : List Instr} {s : State} {Q : State → Prop} (h1 : 1 ≤ n)
    (h2 : n ≤ 31) (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr r >>> n → WP isa (.block is) s1 Q) :
    WP isa (.block (.mov d (.shifted r .lsr n) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, h1, h2, and_self, ite_true, Option.map_some]) k

theorem wp_addReg {d n m : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.reg m) :: is)) s Q :=
  wp_setReg rfl k

theorem wp_addImm {d n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true) (k : ∀ s1, Only [d] s s1 → s1.gpr d = s.gpr n + v → WP isa (.block is) s1 Q) :
    WP isa (.block (.dp .add d n (.imm v) :: is)) s Q :=
  wp_setReg (by simp only [exec, Op2.eval, hv, ite_true, Option.map_some]) k

theorem wp_str {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4)
    (k : ∀ s1, MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.str t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, exec_str ho h, k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem wp_strb {t n : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1)
    (k : ∀ s1, MemTo s s1 (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8)) →
      WP isa (.block is) s1 Q) : WP isa (.block (.strb t n off :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨{ s with mem := s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8) },
    by simp only [exec, ho, ite_true, State.store8, h], k _ ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `cmp n, #v`: the flags only, `Z` set if `n = v`. -/
theorem wp_cmpImm {n : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (hv : encodable v = true)
    (k : ∀ s1, Only [] s s1 → s1.z = (s.gpr n - v == 0) → WP isa (.block is) s1 Q) :
    WP isa (.block (.cmp n (.imm v) :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨subFlags s (s.gpr n) v, by simp only [exec, Op2.eval, hv, ite_true, Option.map_some],
    k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ rfl⟩

end VG.Proof.MlDsa.Arm.Message
