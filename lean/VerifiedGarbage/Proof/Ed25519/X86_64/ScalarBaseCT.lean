import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain

/-! Merged from `Proof.Ed25519.X86_64.PointMulCT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.PointMulCTLoop`. -/
section
/-! Both executions descend through the same public checkpoint count. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem pointMulLoop_ct (s₁ s₂ : State) (base : Addr) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (hn : count ≤ 32) (n : Nat) :
    RelCT isa (fun x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
      PointMulInv s₂ base count scalar₂ p₂ n y) (.loop (pointMulBatch fld) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (fun n x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
    PointMulInv s₂ base count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply VG.RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count
    · have hct := (pointMulBatch_ct (fld := fld) base j (by omega)).mono
        (fun x y (h : PointMulInv s₁ base count scalar₁ p₁ (j + 1) x ∧
            PointMulInv s₂ base count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.scratch, h.1.counter, h.1.d⟩, ⟨h.2.scratch, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      have hw := withRuns hct (fun x y h =>
        ⟨pointMulBatch_ok h.1.scratch j count scalar₁ p₁ hj hn h.1.counter h.1.d h.1.value h.1.bits h.1.table,
         pointMulBatch_ok h.2.scratch j count scalar₂ p₂ hj hn h.2.counter h.2.d h.2.value h.2.bits h.2.table⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, hi, hx, hy⟩
      have ex : eval .ne x = some (!(decide (j = 0))) := by
        simp only [eval, hx.2.1, Option.map_some]
      have ey : eval .ne y = some (!(decide (j = 0))) := by
        simp only [eval, hy.2.1, Option.map_some]
      refine ⟨ex.trans ey.symm, fun _ => trivial, ?_⟩
      intro he
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, decide_true, Bool.not_true] at he
        cases he
      refine ⟨j, by omega, ?_, ?_⟩
      · exact ⟨by omega, by omega, hx.2.2.2.2.2.2.scratch hi.1.scratch, hx.1,
          hx.2.2.2.1, hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
          hi.1.keep.trans hx.2.2.2.2.2.2⟩
      · exact ⟨by omega, by omega, hy.2.2.2.2.2.2.scratch hi.2.scratch, hy.1,
          hy.2.2.2.1, hy.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
          hi.2.keep.trans hy.2.2.2.2.2.2⟩
    · apply VG.RelCT.of_false
      intro x y h
      have := h.1.bound
      omega

end VG.Proof.Ed25519.X86_64
end

/-! Complete secret scalar multiplication has a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

def MulCTPreN (count : Nat) (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scratch s base ∧ scalar < 2 ^ (16 * count) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

abbrev MulCTPre := MulCTPreN 16

theorem pointMultiply_ct_of_init (count : Nat) (base : Addr) (scalar₁ scalar₂ : Nat)
    (hn0 : 0 < count) (hn : count ≤ 32)
    (initCT : RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiplyInit fld count) (fun _ _ => True)) :
    RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiply fld count) (fun _ _ => True) := by
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 count scalar₁ hn0 hn h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 count scalar₂ hn0 hn h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hi ?_
  intro x y tx ty x' y' ⟨_, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base count scalar₁ scalar₂ _ _ hn count _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

theorem pointMultiply16_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiply fld 16) (fun _ _ => True) := by
  have initCT : RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiplyInit fld 16) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  exact pointMultiply_ct_of_init 16 base scalar₁ scalar₂ (by decide) (by decide) initCT

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseCTEngine`. -/
section
/-! Expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

end VG.Proof.Ed25519.X86_64
end

/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

private def BaseStart (base k out : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base

private def BasePrepared (base k out : Addr) (s : State) : Prop :=
  BaseEnginePre base k s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out : Addr} {s : State} (hs : BaseStart base k out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out) := by
  obtain ⟨⟨hr, hw, hd, _, _, hn⟩, ho, hk, hb⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, _⟩ => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, _⟩ => ?_
  rw [ga, hb] at pb ob
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScratch hd hq (by decide)

private theorem start_ct (base k out : Addr) :
    RelCT isa (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y) := by
  have hc : RelCT isa (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi, .rdx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {engine : Prog isa} (engine_ok : BaseEngineCorrect engine) {base k out : Addr} {s : State} (hs : BasePrepared base k out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {engine : Prog isa} (engine_ok : BaseEngineCorrect engine)
    (engine_ct : ∀ base k, RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      engine (fun _ _ => True)) (base k out : Addr) :
    RelCT isa (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k).mono
    (fun _ _ (h : BasePrepared base k out _ ∧ BasePrepared base k out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready engine_ok h.1, engine_ready engine_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .rdx = base ∧ t.gpr .rdi = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine VG.RelCT.seq hc' ?_
  apply taintFld (Taint.ofRegs [.rdx, .rdi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct_of_engine (engine : Prog isa) (engine_ok : BaseEngineCorrect engine)
    (engineCT : ∀ base k, RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      engine (fun _ _ => True)) :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub (scalarBaseWith engine) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct engine_ok engineCT (x.gpr .rdx) (x.gpr .rsi) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm⟩⟩ ex ey

end VG.Proof.Ed25519.X86_64
