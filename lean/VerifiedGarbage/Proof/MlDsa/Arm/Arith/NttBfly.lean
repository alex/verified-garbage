import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt

/-!
# ML-DSA on 32-bit ARM: the butterflies of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. Each butterfly is three
blocks, each symbolically executed once for any state: before `mulz`,
`mulz` (`mulz_ok`), and after it; their values are those of `bfly` and
`bflyInv` (`bfly_spec`, `bflyInv_spec`): what `BflyOk` states of a
butterfly's code, for the loops (`NttLoop.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (addr_ptr inRegions_of)

/-- The pieces of the zeta `z`, and `q`, in `r4`–`r7`. -/
def ZetaIn (z : Zq) (s : State) : Prop :=
  s.gpr .r4 = Qw ∧ s.gpr .r5 = BitVec.ofNat 32 z.val >>> 14 ∧ s.gpr .r6 = BitVec.ofNat 32 z.val <<< 18 >>> 25 ∧
    s.gpr .r7 = BitVec.ofNat 32 z.val <<< 25 >>> 25

/-- The registers the loops of the transforms keep. -/
abbrev bflyKeep : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r11, .lr]

/-- The code `code len` does what the butterfly `op` does, on the
coefficients `j` and `j + len` of the polynomial at `p`, with `r0` pointing
at coefficient `j`, the zeta's pieces in `r5`–`r7`, and `r3` counting down. -/
def BflyOk (code : Nat → List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ (p : BitVec 32) (len j : Nat), 0 < len → len ≤ 128 → j + len < 256 → p.toNat + 1024 ≤ 2 ^ 32 →
    ∀ (z : Zq) (G : Poly) (s : State), s.gpr .r0 = p + BitVec.ofNat 32 (4 * j) → ZetaIn z s →
      PolyIs s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
      WP isa (.block (code len)) s fun s' =>
        PolyIs s'.mem (State.addr p) (op G j len z) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (j + 1)) ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
        s'.z = (s.gpr .r3 - 1 == 0) ∧ Keep bflyKeep s s'

/-! ## Loads, stores and values -/

/-- A pointer to coefficient `j`, plus the offset of coefficient `j + k`. -/
theorem addr_at {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j k : Nat} (h : j + k < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr p) (j + k) := by
  rw [addr_ptr _ _ _ (by omega), ← Nat.mul_add]

theorem addr_at0 {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j : Nat} (h : j < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 0) = coeffAddr (State.addr p) j :=
  addr_at (k := 0) hp h

theorem wr_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions s.wr (coeffAddr (State.addr p) j) 4 :=
  inRegions_of hw (coeff_contains _ h)

theorem rd_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (State.addr p) j) 4 :=
  inRegions_of (List.mem_append_right _ hw) (coeff_contains _ h)

theorem ptr_next (p : BitVec 32) (j : Nat) :
    p + BitVec.ofNat 32 (4 * j) + 4 = p + BitVec.ofNat 32 (4 * (j + 1)) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]

/-- The word stored for a coefficient, as a value of `ℤ_q`. -/
theorem word_val {m : Mem} {P : Addr} {G : Poly} (h : PolyIs m P G) {j : Nat} (hj : j < 256) :
    m.readW (coeffAddr P j) 32 = BitVec.ofNat 32 (G[j]!).val := by
  rw [← coeffAt_eq]; exact ofNat_val_eq (polyIs_toNat h hj)

/-- `csub` after `mulz` of stored values. -/
theorem mulz_val (b z : Zq) :
    bcsub (bmulz (BitVec.ofNat 32 b.val) (BitVec.ofNat 32 z.val >>> 14) (BitVec.ofNat 32 z.val <<< 18 >>> 25)
      (BitVec.ofNat 32 z.val <<< 25 >>> 25)) = BitVec.ofNat 32 (z * b).val := by
  refine ofNat_val_eq ?_
  rw [bcsub_mulz (by rw [toNat_val]; exact b.isLt) (by rw [toNat_val]; exact z.isLt), toNat_val, toNat_val,
    val_mul, Nat.mul_comm]

theorem sub_val (a t : Zq) : bfix (BitVec.ofNat 32 a.val - BitVec.ofNat 32 t.val) = BitVec.ofNat 32 (a - t).val := by
  refine ofNat_val_eq ?_
  rw [bfix_sub (by rw [toNat_val]; exact a.isLt) (by rw [toNat_val]; exact t.isLt), toNat_val, toNat_val, val_sub',
    Nat.add_sub_assoc (Nat.le_of_lt t.isLt)]

theorem add_val (a t : Zq) : bcsub (BitVec.ofNat 32 a.val + BitVec.ofNat 32 t.val) = BitVec.ofNat 32 (a + t).val := by
  refine ofNat_val_eq ?_
  rw [bcsub_add (by rw [toNat_val]; exact a.isLt) (by rw [toNat_val]; exact t.isLt), toNat_val, toNat_val, val_add']

/-! ## `NTT` -/

/-- The butterfly of `NTT` after the load and `mulz`. -/
def bflyRest (len : Nat) : List Instr :=
  csub .r9 .r12 .r4 ++ [.ldr .r8 .r0 0, .dp .sub .r10 .r8 (.reg .r9)] ++ fixup .r10 .r12 .r4 ++
    [.str .r10 .r0 (4 * len), .dp .add .r8 .r8 (.reg .r9)] ++ csub .r8 .r12 .r4 ++
    [.str .r8 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bfly_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bfly len = ([.ldr .r8 .r0 (4 * len)] : List Instr) ++ (mulz .r9 .r8 .r12 ++ bflyRest len) := by
  simp only [Impl.MlDsa.Arm.Arith.bfly, bflyRest, List.append_assoc, List.cons_append, List.nil_append]

section
variable {s : State} {x c v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = v)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h4 h9 iA oA oB

theorem bflyRest_ok :
    WP isa (.block (bflyRest len)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len)))
          (bfix (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 - bcsub v))).writeW
        (State.addr (x + BitVec.ofNat 32 0)) (bcsub (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + bcsub v)) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ Keep bflyKeep s s' := by
  run_block [bflyRest, csub, fixup, bcsub, bfix, Keep, h0, h3, h4, h9, iA, oA, oB, hlen, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

theorem bfly_spec : BflyOk Impl.MlDsa.Arm.Arith.bfly VG.Proof.MlDsa.Arith.bfly := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := addr_at hp hj (j := j) (k := len)
  have eA := addr_at0 hp (j := j) (by omega)
  rw [bfly_split, WP.block_append_iff]
  have iB : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 4 := by
    rw [h0, eB]; exact rd_at hw hj
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr (by omega) iB, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (s := s.setReg .r8 _) (b := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 32)
    (z₂ := BitVec.ofNat 32 z.val >>> 14) (z₁ := BitVec.ofNat 32 z.val <<< 18 >>> 25)
    (z₀ := BitVec.ofNat 32 z.val <<< 25 >>> 25) (by simp [State.setReg, z4]) (by simp [State.setReg, z5])
    (by simp [State.setReg, z6]) (by simp [State.setReg, z7]) (by simp [State.setReg]))
    fun s₁ ⟨e9, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₁.gpr r = s.gpr r := fun r a8 a9 a12 => by
    rw [eo r a9 a12]; simp [State.setReg, a8]
  have hw₁ : polyRegion (State.addr p) ∈ s₁.wr := by rw [wr₁]; exact hw
  refine WP.mono (bflyRest_ok (s := s₁) (x := p + BitVec.ofNat 32 (4 * j)) (by omega)
    ((g _ (by decide) (by decide) (by decide)).trans h0) rfl ((g _ (by decide) (by decide) (by decide)).trans z4)
    e9 (by rw [eA]; exact rd_at hw₁ (by omega)) (by rw [eA]; exact wr_at hw₁ (by omega))
    (by rw [eB]; exact wr_at hw₁ hj)) fun s' ⟨hm, r0, r3, hzf, hk⟩ => ?_
  have nk : ∀ r ∈ bflyKeep, r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₁ : Keep bflyKeep s s₁ := ⟨fun r hr => g r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₁, wr₁, sp₁⟩
  have e3 : s₁.gpr .r3 = s.gpr .r3 := g _ (by decide) (by decide) (by decide)
  have hjn : j < n := by rw [n_eq]; omega
  have hjl : j + len < n := by rw [n_eq]; omega
  refine ⟨?_, ?_, by rw [r0]; exact ptr_next p j, by rw [r3, e3], by rw [hzf, e3], k₁.trans hk⟩
  · rw [hm, m₁, eA, eB]
    simp only [State.setReg]
    rw [h0, eB, word_val hG hj, word_val hG (by omega), mulz_val, sub_val, add_val]
    have h1 := polyIs_writeW hG hj (G[j]! - z * G[j + len]!) (toNat_val _)
    have h2 := polyIs_writeW h1 hjn (G[j]! + z * G[j + len]!) (toNat_val _)
    simp only [VG.Proof.MlDsa.Arith.bfly]
    rwa [getElem!_set!_ne _ hjn (by omega)]
  · rw [hm, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

/-! ## `NTT⁻¹` -/

/-- The butterfly of `NTT⁻¹` before `mulz`. -/
def bflyInvPre (len : Nat) : List Instr :=
  [.ldr .r8 .r0 0, .ldr .r9 .r0 (4 * len), .dp .add .r10 .r8 (.reg .r9)] ++ csub .r10 .r12 .r4 ++
    [.str .r10 .r0 0, .dp .sub .r8 .r8 (.reg .r9)] ++ fixup .r8 .r12 .r4

/-- The butterfly of `NTT⁻¹` after `mulz`. -/
def bflyInvPost (len : Nat) : List Instr :=
  csub .r9 .r12 .r4 ++ [.str .r9 .r0 (4 * len), .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bflyInv_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bflyInv len = bflyInvPre len ++ (mulz .r9 .r8 .r12 ++ bflyInvPost len) := by
  simp only [Impl.MlDsa.Arm.Arith.bflyInv, bflyInvPre, bflyInvPost, List.append_assoc, List.cons_append,
    List.nil_append]

section
variable {s : State} {x : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h4 : s.gpr .r4 = Qw)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include hlen h0 h4 iA iB oA

theorem bflyInvPre_ok :
    WP isa (.block (bflyInvPre len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (bcsub (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32)) ∧
      s'.gpr .r8 = bfix (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32) ∧
      s'.gpr .r0 = x ∧ s'.gpr .r3 = s.gpr .r3 ∧ Keep bflyKeep s s' := by
  run_block [bflyInvPre, csub, fixup, bcsub, bfix, h0, h4, iA, iB, oA, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

section
variable {s : State} {x c v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = v)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h4 h9 oB

theorem bflyInvPost_ok :
    WP isa (.block (bflyInvPost len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len))) (bcsub v) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ Keep bflyKeep s s' := by
  run_block [bflyInvPost, csub, fixup, bcsub, bfix, h0, h3, h4, h9, oB, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

/-- The inverse butterfly as two writes. -/
theorem bflyInv_eq (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    VG.Proof.MlDsa.Arith.bflyInv G j len z =
      (G.set! j (G[j]! + G[j + len]!)).set! (j + len) (z * (G[j]! - G[j + len]!)) := by
  refine ext_getElem! fun i hi => ?_
  rw [bflyInv_get _ hl hj _ hi]
  rcases (by omega : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨h1, h2⟩
  · rw [ite_eq_left rfl, getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi]
  · rw [ite_eq_right (by omega), ite_eq_left rfl, getElem!_set!_self _ hi]
  · rw [ite_eq_right h1, ite_eq_right h2, getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h1)]

theorem bflyInv_spec : BflyOk Impl.MlDsa.Arm.Arith.bflyInv VG.Proof.MlDsa.Arith.bflyInv := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := addr_at hp hj (j := j) (k := len)
  have eA := addr_at0 hp (j := j) (by omega)
  have hjn : j < n := by rw [n_eq]; omega
  have hjl : j + len < n := by rw [n_eq]; omega
  rw [bflyInv_split, WP.block_append_iff]
  refine WP.mono (bflyInvPre_ok (len := len) (by omega) h0 z4 (by rw [eA]; exact rd_at hw hjn)
    (by rw [eB]; exact rd_at hw hj) (by rw [eA]; exact wr_at hw hjn)) fun s₁ ⟨m₁, e8, e0, e3, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (k₁.gpr .r4 (by decide) ▸ z4) (k₁.gpr .r5 (by decide) ▸ z5)
    (k₁.gpr .r6 (by decide) ▸ z6) (k₁.gpr .r7 (by decide) ▸ z7) e8)
    fun s₂ ⟨e9, eo, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have nk : ∀ r ∈ bflyKeep, r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₂ : Keep bflyKeep s₁ s₂ := ⟨fun r hr => eo r (nk r hr).1 (nk r hr).2, rd₂, wr₂, sp₂⟩
  have hw₂ : polyRegion (State.addr p) ∈ s₂.wr := by rw [k₂.wr, k₁.wr]; exact hw
  refine WP.mono (bflyInvPost_ok (s := s₂) (x := p + BitVec.ofNat 32 (4 * j)) (len := len) (by omega)
    ((eo _ (by decide) (by decide)).trans e0) rfl ((k₁.trans k₂).gpr .r4 (by decide) ▸ z4) e9
    (by rw [eB]; exact wr_at hw₂ hj)) fun s' ⟨hm, r0, r3, hzf, k₃⟩ => ?_
  have e3' : s₂.gpr .r3 = s.gpr .r3 := (eo _ (by decide) (by decide)).trans e3
  refine ⟨?_, ?_, by rw [r0]; exact ptr_next p j, by rw [r3, e3'], by rw [hzf, e3'], (k₁.trans k₂).trans k₃⟩
  · rw [hm, m₂, m₁, eA, eB, word_val hG hjn, word_val hG hj, add_val, sub_val, mulz_val, bflyInv_eq _ hl hjl]
    have h1 := polyIs_writeW hG hjn (G[j]! + G[j + len]!) (toNat_val _)
    exact polyIs_writeW h1 hjl (z * (G[j]! - G[j + len]!)) (toNat_val _)
  · rw [hm, m₂, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)

end VG.Proof.MlDsa.Arm.Arith
