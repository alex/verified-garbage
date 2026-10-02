import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Sha3.X86_64.X4

/-!
# Keccak-f[1600] four times at once on x86-64: one instruction at a time

Weakest-precondition rules for the AVX2 instructions of `permute4`, in terms
of the four 64-bit elements of each `ymm` register (`q4`), one per state.
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4

/-- Element `k` (`k < 4`) of `ymm r`: lane `j` of state `k`, when `r` holds
lane `j` of the four states. -/
def q4 (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.lane r (k / 2)) (k % 2)

/-! ## Quadwords of values -/

@[simp] theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem qword_app1 (a b : BitVec 64) : qword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_or (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_andn (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (~~~x &&& y) i = ~~~qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj, show 64 * i + j < 128 by omega]

theorem qword_psllq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psllq x n) i = qword x i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem qword_psrlq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x n) i = qword x i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem mod2_lt (k : Nat) : k % 2 < 2 := Nat.mod_lt _ (by decide)

theorem cases4 {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem ymm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (128 * l) 128 = s.lane r l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hj]

/-- Element `k` of a 256-bit register, as bits of the whole. -/
theorem q4_ymm (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (s.ymm r).extractLsb' (64 * k) 64 = q4 s r k := by
  rw [q4, ← ymm_lane _ _ (show k / 2 < 2 by omega), qword, extract_extract _ _ _ _ _ (by omega)]
  congr 1; omega

/-- A ROTL by `n` as the two shifts. -/
theorem shr_or_shl (v : BitVec 64) {n : Nat} (h₁ : 0 < n) (h₂ : n < 64) :
    v >>> (64 - n) ||| v <<< n = v.rotateRight (64 - n) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt (by omega), show 64 - (64 - n) = n by omega]

/-! ## The machine -/

/-- `s'` is `s` with `ymm d` set to the four elements `v` (flags aside). -/
structure VUpd (s s' : State) (d : XReg) (v : Nat → BitVec 64) : Prop where
  val : ∀ k < 4, q4 s' d k = v k
  other : ∀ r, r ≠ d → ∀ k < 4, q4 s' r k = q4 s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VUpd.trans {s₁ s₂ s₃ : State} {d : XReg} {v w : Nat → BitVec 64} (h₁ : VUpd s₁ s₂ d v)
    (h₂ : VUpd s₂ s₃ d w) : VUpd s₁ s₃ d w :=
  ⟨h₂.val, fun r h k hk => (h₂.other r h k hk).trans (h₁.other r h k hk), h₂.gpr.trans h₁.gpr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem q4_vbin (op : VBinOp) (s : State) (d a b r : XReg) (k : Nat) :
    q4 ((VOp.vbin op .l256 d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) else q4 s r k := by
  simp only [q4, lane_vbin256]
  split <;> rfl

theorem q4_vshift (op : XShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) (k : Nat) :
    q4 ((VOp.vshift op .l256 d a n).exec s) r k =
      if r = d then qword (op.eval (s.lane a (k / 2)) n) (k % 2) else q4 s r k := by
  simp only [q4, lane_vshift256]
  split <;> rfl

theorem VUpd.vbin (op : VBinOp) (s : State) (d a b : XReg) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) = v k) :
    VUpd s ((VOp.vbin op .l256 d a b).exec s) d v :=
  ⟨fun k hk => by rw [q4_vbin, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [q4_vbin, ite_eq_right hr], VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩

theorem VUpd.vshift (op : XShiftOp) (s : State) (d a : XReg) (n : BitVec 8) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword (op.eval (s.lane a (k / 2)) n) (k % 2) = v k) :
    VUpd s ((VOp.vshift op .l256 d a n).exec s) d v :=
  ⟨fun k hk => by rw [q4_vshift, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [q4_vshift, ite_eq_right hr], VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vxor {d a b : XReg} (k : ∀ s', VUpd s s' d (fun i => q4 s a i ^^^ q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpxor d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by simp only [VBinOp.sse, XBinOp.eval, qword_xor]; rfl))

theorem wp_vor {d a b : XReg} (k : ∀ s', VUpd s s' d (fun i => q4 s a i ||| q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpor d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by simp only [VBinOp.sse, XBinOp.eval, qword_or]; rfl))

theorem wp_vandn {d a b : XReg}
    (k : ∀ s', VUpd s s' d (fun i => ~~~q4 s a i &&& q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpandn d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by
    simp only [VBinOp.sse, XBinOp.eval]; rw [qword_andn _ _ (mod2_lt _)]; rfl))

theorem wp_vshl {d a : XReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', VUpd s s' d (fun i => q4 s a i <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (vsh .psllq d a n :: is)) s Q := by
  have e : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  exact WP.cons rfl (k _ (VUpd.vshift _ _ _ _ _ fun _ _ => by
    rw [qword_psllq _ (by omega) (mod2_lt _), e]; rfl))

theorem wp_vshr {d a : XReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', VUpd s s' d (fun i => q4 s a i >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (vsh .psrlq d a n :: is)) s Q := by
  have e : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  exact WP.cons rfl (k _ (VUpd.vshift _ _ _ _ _ fun _ _ => by
    rw [qword_psrlq _ (by omega) (mod2_lt _), e]; rfl))

theorem wp_vmovq {d : XReg} {g : Reg}
    (k : ∀ s', VUpd s s' d (fun i => if i = 0 then s.gpr g else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vmovq d g) :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩)
  · simp only [VOp.exec, q4, State.lane_setV128, ite_true]
    rcases cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [qword_app0, qword_app1, Nat.reduceDiv, Nat.reduceMod, ite_true, ite_false,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide] <;> simp [qword]
  · simp only [VOp.exec, q4, State.lane_setV128, ite_eq_right hr]

theorem wp_vbcast {d a : XReg}
    (k : ∀ s', VUpd s s' d (fun _ => q4 s a 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastq .l256 d a) :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩)
  · simp only [VOp.exec, q4, State.lane_setV256, ite_true]
    have : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> split <;> simp [State.lane]
  · simp only [VOp.exec, q4, State.lane_setV256, ite_eq_right hr]

theorem wp_vld {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', VUpd s s' d (fun i => s.mem.readW (a + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp only [exec, ha, State.load256, hin, ite_true,
      Option.map_some]) (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, by simp, by simp, by simp, by simp⟩)
  · simp only [q4, State.lane_setV256, ite_true]
    have e : (if i / 2 = 0 then (s.mem.readW a 256).extractLsb' 0 128 else (s.mem.readW a 256).extractLsb' 128 128) =
        (s.mem.readW a 256).extractLsb' (128 * (i / 2)) 128 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword, extract_extract _ _ _ _ _ (by omega),
      show 128 * (i / 2) + 64 * (i % 2) = 8 * (8 * i) by omega]
    exact readW_extract _ _ (k := 8 * i) (n := 8) (by omega)
  · simp only [q4, State.lane_setV256, ite_eq_right hr]

theorem wp_vst {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x j, q4 s' x j = q4 s x j) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

end

/-- Element `k` of a stored register, read back. -/
theorem readW_st (m : Mem) (a : Addr) (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.ymm r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = q4 s r k := by
  have e := readW_writeW_inside m a (s.ymm r) (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega, q4_ymm _ _ hk] at e
  exact e

end VG.Proof.Sha3.X86_64.X4
