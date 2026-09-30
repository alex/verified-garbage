import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2

/-!
# Poly1305 on x86-64 with AVX2: straight-line code, quadword by quadword

Untrusted: everything here is checked by Lean. The vector code of
`vg_poly1305_blocks_avx2` moves, adds, multiplies, masks and shifts the four
quadwords of `ymm` registers, and loads 64 bytes at `rsi`. `Sym.run`
computes each quadword after a block of such instructions as a term (`Q`) in
the quadwords, general-purpose registers and memory before it, and `srun_ok`
proves the machine agrees. Every instruction but the loads, `vpermq`,
`vpunpck{l,h}qdq`, `vmovq` and `vpbroadcastq` acts on each quadword on its
own, so a term is evaluated at a quadword (a lane) `k < 4`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64

/-! ## Registers and quadwords -/

/-- The vector register numbered `i`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- The number of a vector register. -/
def xi : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

theorem xr_xi (r : XReg) : xr (xi r) = r := by cases r <;> rfl

theorem xi_inj {r r' : XReg} : xi r = xi r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

/-- Quadword `k` (`k < 4`) of `ymm r`. -/
def qw (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.lane r (k / 2)) (k % 2)

theorem cases4 {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

/-! ### Quadwords of values -/

@[simp] theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem qword_app1 (a b : BitVec 64) : qword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem qword_eq (v : BitVec 128) (i : Nat) : qword v i = dword v (2 * i + 1) ++ dword v (2 * i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  by_cases h : j < 32
  · simp only [h, ite_true, decide_true, Bool.true_and]; congr 1; omega
  · simp only [h, ite_false, decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]; congr 1; omega

theorem qword_and (x y : BitVec 128) (i : Nat) : qword (x &&& y) i = qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_or (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_andn (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (~~~x &&& y) i = ~~~qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj, show 64 * i + j < 128 by omega]

theorem dword_lo (x : BitVec 128) (i : Nat) : dword x (2 * i) = (qword x i).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 0 + j < 64 by omega)]
  exact congrArg _ (by omega)

theorem dword_hi (x : BitVec 128) (i : Nat) : dword x (2 * i + 1) = (qword x i).extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 32 + j < 64 by omega)]
  exact congrArg _ (by omega)

/-- The low doubleword of a quadword, zero-extended. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x.extractLsb' 0 32).setWidth 64

theorem qword_paddq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .paddq x y) i = qword x i + qword y i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_pmuludq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pmuludq x y) i = lo32 (qword x i) * lo32 (qword y i) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [XBinOp.eval, qword_app0, lo32, ← dword_lo]
  · simp only [XBinOp.eval, qword_app1, lo32, ← dword_lo]

theorem qword_punpcklqdq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .punpcklqdq x y) i = if i = 0 then qword x 0 else qword y 0 := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_punpckhqdq (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .punpckhqdq x y) i = if i = 0 then qword x 1 else qword y 1 := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [XBinOp.eval]

theorem qword_psllq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psllq x n) i = qword x i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem qword_psrlq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x n) i = qword x i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

/-- A quadword from its doublewords picked by two selector bits. -/
def pick2 (a b : BitVec 64) (lo hi : Bool) : BitVec 64 :=
  (if hi then b.extractLsb' 32 32 else a.extractLsb' 32 32) ++
    (if lo then b.extractLsb' 0 32 else a.extractLsb' 0 32)

theorem qword_ofDwords (a b c d : BitVec 32) {i : Nat} (hi : i < 2) :
    qword (ofDwords a b c d) i = if i = 0 then b ++ a else d ++ c := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rw [qword_eq] <;> simp

theorem qword_blendDwords (x y : BitVec 128) (imm : BitVec 4) {i : Nat} (hi : i < 2) :
    qword (blendDwords x y imm) i =
      pick2 (qword x i) (qword y i) (imm.getLsbD (2 * i)) (imm.getLsbD (2 * i + 1)) := by
  simp only [blendDwords]
  rw [qword_ofDwords _ _ _ _ hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [ite_true, pick2, ← dword_lo, ← dword_hi, Nat.mul_zero, Nat.zero_add]
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, pick2, ← dword_lo, ← dword_hi]

/-- Quadword `k` (`k < 4`) of a 256-bit value. -/
theorem qword256_eq (x : BitVec 256) (k : Nat) :
    qword256 x k = qword (x.extractLsb' (128 * (k / 2)) 128) (k % 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * (k % 2) + j < 128 by omega)]
  congr 1; omega

theorem qword256_ymm (s : State) (r : XReg) {k : Nat} (hk : k < 4) : qword256 (s.ymm r) k = qw s r k := by
  rw [qword256_eq, qw]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp [hj]

theorem qword256_cat (a b c d : BitVec 64) {k : Nat} (hk : k < 4) :
    qword256 (a ++ b ++ c ++ d) k = if k = 0 then d else if k = 1 then c else if k = 2 then b else a := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have e : (a ++ b ++ c ++ d).toNat = ((a.toNat * 2 ^ 64 + b.toNat) * 2 ^ 64 + c.toNat) * 2 ^ 64 + d.toNat := by
    rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, ← Nat.shiftLeft_add_eq_or_of_lt c.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt d.isLt]
    simp only [Nat.shiftLeft_eq]
  simp only [qword256, BitVec.extractLsb'_toNat, e, Nat.shiftRight_eq_div_pow]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- The selector of quadword `k` in `vpermq`'s immediate. -/
def sel4 (o k : Nat) : Nat := o / 4 ^ k % 4

theorem sel4_lt (o k : Nat) : sel4 o k < 4 := Nat.mod_lt _ (by decide)

theorem qword256_perm (x : BitVec 256) (o : BitVec 8) {k : Nat} (hk : k < 4) :
    qword256 (permQwords x o) k = qword256 x (sel4 o.toNat k) := by
  have e : ∀ i, (o.extractLsb' (2 * i) 2).toNat = sel4 o.toNat i := fun i => by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul, sel4]
  simp only [permQwords, qword256_cat _ _ _ _ hk, e]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-! ### Quadwords of registers after an instruction -/

theorem qw_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (k : Nat) :
    qw (s.setV .l256 d lo hi) r k = if r = d then qword (if k / 2 = 0 then lo else hi) (k % 2) else qw s r k := by
  simp only [qw, State.lane_setV256]
  split <;> rfl

theorem qw_setV128 (s : State) (d r : XReg) (lo hi : BitVec 128) (k : Nat) :
    qw (s.setV .l128 d lo hi) r k = if r = d then (if k / 2 = 0 then qword lo (k % 2) else 0) else qw s r k := by
  simp only [qw, State.lane_setV128]
  split
  · split
    · rfl
    · simp [qword]
  · rfl

/-- `qw` of the lane of `k`. -/
theorem qw_lane (s : State) (r : XReg) (k : Nat) : qword (s.lane r (k / 2)) (k % 2) = qw s r k := rfl

theorem lane_sel (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (if k / 2 = 0 then s.lane r 0 else s.lane r 1) = s.lane r (k / 2) := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem qw_vbin (op : VBinOp) (s : State) (d a b r : XReg) (k : Nat) :
    qw ((VOp.vbin op .l256 d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) else qw s r k := by
  simp only [qw, lane_vbin256]
  split <;> rfl

theorem qw_vshift (op : XShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) (k : Nat) :
    qw ((VOp.vshift op .l256 d a n).exec s) r k =
      if r = d then qword (op.eval (s.lane a (k / 2)) n) (k % 2) else qw s r k := by
  simp only [qw, lane_vshift256]
  split <;> rfl

theorem qw_vmovdqa (s : State) (d a r : XReg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vmovdqa .l256 d a).exec s) r k = if r = d then qw s a k else qw s r k := by
  simp only [VOp.exec, qw_setV256, lane_sel _ _ hk, qw_lane]

theorem getLsbD_nibble (n : BitVec 8) (l j : Nat) (hj : j < 4) :
    (n.extractLsb' (4 * l) 4).getLsbD j = n.toNat.testBit (4 * l + j) := by
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, BitVec.testBit_toNat]

theorem qw_vpblendd (s : State) (d a b r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpblendd .l256 d a b n).exec s) r k =
      if r = d then pick2 (qw s a k) (qw s b k) (n.toNat.testBit (2 * k)) (n.toNat.testBit (2 * k + 1))
      else qw s r k := by
  simp only [VOp.exec, qw_setV256]
  split
  · have e : (if k / 2 = 0 then blendDwords (s.lane a 0) (s.lane b 0) (n.extractLsb' 0 4)
        else blendDwords (s.lane a 1) (s.lane b 1) (n.extractLsb' 4 4)) =
        blendDwords (s.lane a (k / 2)) (s.lane b (k / 2)) (n.extractLsb' (4 * (k / 2)) 4) := by
      rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword_blendDwords _ _ _ (Nat.mod_lt _ (by decide)), qw_lane, qw_lane,
      getLsbD_nibble _ _ _ (by omega), getLsbD_nibble _ _ _ (by omega),
      show 4 * (k / 2) + 2 * (k % 2) = 2 * k by omega,
      show 4 * (k / 2) + (2 * (k % 2) + 1) = 2 * k + 1 by omega]
  · rfl

theorem qw_vpbroadcastq (s : State) (d a r : XReg) (k : Nat) :
    qw ((VOp.vpbroadcastq .l256 d a).exec s) r k = if r = d then qw s a 0 else qw s r k := by
  simp only [VOp.exec, qw_setV256]
  split
  · have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> split <;> simp [qw, State.lane]
  · rfl

theorem qw_vmovq (s : State) (d r : XReg) (g : Reg) {k : Nat} (hk : k < 4) :
    qw ((VOp.vmovq d g).exec s) r k = if r = d then (if k = 0 then s.gpr g else 0) else qw s r k := by
  simp only [VOp.exec, qw_setV128]
  split
  · rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp
  · rfl

theorem qw_vpermq (s : State) (d a r : XReg) (o : BitVec 8) {k : Nat} (hk : k < 4) :
    qw ((VOp.vpermq d a o).exec s) r k = if r = d then qw s a (sel4 o.toNat k) else qw s r k := by
  simp only [VOp.exec, qw_setV256]
  split
  · rw [← qword256_ymm _ _ (sel4_lt _ _), ← qword256_perm _ _ hk, qword256_eq]
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem qw_load (s : State) (d r : XReg) (a : Addr) {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qw s r k := by
  rw [qw_setV256]
  split
  · have e : (if k / 2 = 0 then (s.mem.readW a 256).extractLsb' 0 128 else (s.mem.readW a 256).extractLsb' 128 128) =
        (s.mem.readW a 256).extractLsb' (128 * (k / 2)) 128 := by
      rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, ← qword256_eq, qword256, show 64 * k = 8 * (8 * k) by omega]
    exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)
  · rfl

/-! ## Terms -/

/-- A quadword, in terms of those where the code starts. -/
inductive Q
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- A general-purpose register, in every quadword. -/
  | gpr (r : Reg)
  /-- `a` in quadword 0, zero elsewhere. -/
  | lane0 (a : Q)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : Q)
  /-- Quadword `i + k` of memory at `rsi`. -/
  | ld (i : Nat)
  | add (a b : Q)
  /-- The product of the low doublewords. -/
  | mul (a b : Q)
  | and (a b : Q)
  /-- `~a & b`. -/
  | andn (a b : Q)
  | or (a b : Q)
  | shl (a : Q) (n : Nat)
  | shr (a : Q) (n : Nat)
  /-- `vpunpcklqdq`, `vpunpckhqdq`. -/
  | unpl (a b : Q)
  | unph (a b : Q)
  /-- `vpermq` with the immediate `o`. -/
  | perm (a : Q) (o : Nat)
  /-- `vpblendd` with the immediate `sel`. -/
  | blend (a b : Q) (sel : Nat)
  deriving DecidableEq, Repr

def Q.eval (s₀ : State) : Q → Nat → BitVec 64
  | .reg r, k => qw s₀ (xr r) k
  | .gpr r, _ => s₀.gpr r
  | .lane0 a, k => if k = 0 then a.eval s₀ 0 else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld i, k => s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * (i + k))) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .mul a b, k => lo32 (a.eval s₀ k) * lo32 (b.eval s₀ k)
  | .and a b, k => a.eval s₀ k &&& b.eval s₀ k
  | .andn a b, k => ~~~a.eval s₀ k &&& b.eval s₀ k
  | .or a b, k => a.eval s₀ k ||| b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .unpl a b, k => if k % 2 = 0 then a.eval s₀ k else b.eval s₀ (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.eval s₀ (k + 1) else b.eval s₀ k
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .blend a b sel, k => pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))

/-! ## The machine -/

/-- The terms of the vector registers (by number). -/
structure Sym where
  reg : Nat → Q

def Sym.init : Sym := ⟨.reg⟩

def Sym.set (σ : Sym) (d : XReg) (t : Q) : Sym := ⟨fun r => if r = xi d then t else σ.reg r⟩

def Sym.bin (σ : Sym) (op : VBinOp) (d a b : XReg) : Option Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpmuludq => some (σ.set d (.mul A B))
  | .vpand => some (σ.set d (.and A B))
  | .vpandn => some (σ.set d (.andn A B))
  | .vpor => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.shift (σ : Sym) (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Option Sym :=
  if n.toNat < 64 then
    match op with
    | .psllq => some (σ.set d (.shl (σ.reg (xi a)) n.toNat))
    | .psrlq => some (σ.set d (.shr (σ.reg (xi a)) n.toNat))
    | _ => none
  else none

def Sym.vop (σ : Sym) : VOp → Option Sym
  | .vbin op .l256 d a b => σ.bin op d a b
  | .vshift op .l256 d a n => σ.shift op d a n
  | .vmovdqa .l256 d a => some (σ.set d (σ.reg (xi a)))
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (xi a)) (σ.reg (xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vmovq d r => some (σ.set d (.lane0 (.gpr r)))
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (xi a)) o.toNat))
  | _ => none

/-- A load of 32 bytes at `rsi + 8 i` (for `i` 0 or 4). -/
def ldIdx (m : MemOp) : Option Nat :=
  if m.base = .rsi ∧ m.index = none then
    if m.disp = 0 then some 0 else if m.disp = 32 then some 4 else none
  else none

/-- One instruction; loads only if `ld`. -/
def Sym.step (ld : Bool) (σ : Sym) : Instr → Option Sym
  | .vop o => σ.vop o
  | .vmovdquLoad .l256 d m => if ld then (ldIdx m).map fun i => σ.set d (.ld i) else none
  | _ => none

def Sym.run (ld : Bool) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step ld i).bind fun σ' => σ'.run ld is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers of `s`. -/
def vec (s₀ s : State) : State := { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi }

theorem vec_vop {s₀ s : State} (h : vec s₀ s = s) (o : VOp) : vec s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vec_setV {s₀ s : State} (h : vec s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vec s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem vec_trans {s₀ s₁ s₂ : State} (h₁ : vec s₀ s₁ = s₁) (h₂ : vec s₁ s₂ = s₂) : vec s₀ s₂ = s₂ := by
  rw [← h₂, ← h₁]; rfl

theorem vec_gpr {s₀ s : State} (h : vec s₀ s = s) : s.gpr = s₀.gpr := by rw [← h]; rfl
theorem vec_mem {s₀ s : State} (h : vec s₀ s = s) : s.mem = s₀.mem := by rw [← h]; rfl
theorem vec_rd {s₀ s : State} (h : vec s₀ s = s) : s.rd = s₀.rd := by rw [← h]; rfl
theorem vec_wr {s₀ s : State} (h : vec s₀ s = s) : s.wr = s₀.wr := by rw [← h]; rfl

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qw s r k = (σ.reg (xi r)).eval s₀ k
  eq : vec s₀ s = s

theorem SRel.gpr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem SRel.mem {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem SRel.rd {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, Q.eval, xr_xi], rfl⟩

theorem SRel.set {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {d : XReg} {t : Q} {s' : State}
    (hv : ∀ r k, k < 4 → qw s' r k = if r = d then t.eval s₀ k else qw s r k)
    (he : vec s₀ s' = s') : SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk


/-- What the loads may read: 64 bytes at `rsi`. -/
def Ctx (s₀ : State) : Prop :=
  ∀ i, i = 0 ∨ i = 4 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 32

theorem ldIdx_ok {m : MemOp} {i : Nat} (h : ldIdx m = some i) :
    (i = 0 ∨ i = 4) ∧ ∀ s : State, s.ea m = s.gpr .rsi + BitVec.ofNat 64 (8 * i) := by
  unfold ldIdx at h
  split at h
  · rename_i hb
    split at h
    · cases h
      refine ⟨.inl rfl, fun s => ?_⟩
      simp only [State.ea, hb.2, hb.1, *]; rfl
    · split at h
      · cases h
        refine ⟨.inr rfl, fun s => ?_⟩
        simp only [State.ea, hb.2, hb.1, *]; rfl
      · cases h
  · cases h

theorem hv_of {s s' : State} {d : XReg} {f : Nat → BitVec 64} (hd : ∀ k, k < 4 → qw s' d k = f k)
    (ho : ∀ r, r ≠ d → ∀ k, k < 4 → qw s' r k = qw s r k) :
    ∀ r k, k < 4 → qw s' r k = if r = d then f k else qw s r k := by
  intro r k hk
  by_cases hr : r = d
  · subst hr; rw [ite_eq_left rfl]; exact hd k hk
  · rw [ite_eq_right hr]; exact ho r hr k hk

theorem mod2_lt (k : Nat) : k % 2 < 2 := Nat.mod_lt _ (by decide)

theorem sstep_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) {i : Instr} (e : σ.step ld i = some σ') : ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.reg (xi a)).eval s₀ k = qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := vec_vop h.eq o
    unfold Sym.vop at e
    split at e
    · rename_i op d a b
      unfold Sym.bin at e
      split at e <;> cases e <;>
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he <;>
        rw [qw_vbin, ite_eq_left rfl] <;> simp only [VBinOp.sse, Q.eval]
      · rw [qword_paddq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [qword_pmuludq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_and, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_andn _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_or, qw_lane, qw_lane, hR a k hk, hR b k hk]
      · rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, qw, h0]
        · rw [hR b (k - 1) (by omega), qw, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), qw, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, qw, show k % 2 = 1 by omega]
    · rename_i op d a n
      unfold Sym.shift at e
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vshift, ite_eq_right hr])) he <;>
          rw [qw_vshift, ite_eq_left rfl] <;> simp only [Q.eval]
        · rw [qword_psllq _ hn (mod2_lt k), qw_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), qw_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [qw_vmovdqa _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a b n
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k _ => by rw [qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [qw_vpbroadcastq, ite_eq_right hr])) he
    · rename_i d g
      cases e
      exact h.set (hv_of (fun k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, h.gpr])
        (fun r hr k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a o
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval]; rw [hR a _ (sel4_lt _ _)])
        (fun r hr k hk => by rw [qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he
    · cases e
  · rename_i d m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hi, hea⟩ := ldIdx_ok hs
    have ea : s.ea m = s₀.gpr .rsi + BitVec.ofNat 64 (8 * i) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 32 := by
      rw [h.rd, h.wr]; exact hc hld i hi
    refine ⟨s.setV .l256 d ((s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 256).extractLsb' 0 128)
      ((s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some], ?_⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qw_load _ _ _ _ hk, ite_eq_right hr]))
      (vec_setV h.eq _ _ _ _)
    rw [qw_load _ _ _ _ hk, ite_eq_left rfl, h.mem, Offset.add_add]; simp only [Q.eval, Nat.mul_add]
  · cases e

/-- A block of instructions. -/
theorem srun_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.run ld is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) {is : List Instr} {σ : Sym}
    (e : Sym.init.run ld is = some σ) : WP isa (.block is) s₀ (SRel σ s₀) :=
  srun_ok hc is (SRel.init s₀) e

end VG.Proof.Poly1305.X86_64.Avx2
