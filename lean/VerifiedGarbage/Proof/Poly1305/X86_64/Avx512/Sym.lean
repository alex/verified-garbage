import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512

/-!
# Poly1305 on x86-64 with AVX-512: straight-line code, quadword by quadword

Untrusted: everything here is checked by Lean. The vector code of
`vg_poly1305_blocks_avx512` moves, adds, multiplies, masks, shifts and
shuffles the eight quadwords of `zmm` registers, and loads 128 bytes at
`rsi`. As for AVX2 (`Avx2/Sym.lean`), `Sym.run` computes each quadword after
a block of such instructions as a term (`Q`) in the quadwords, general-purpose
registers and memory before it, and `srun_ok` proves the machine agrees.
Every instruction but the loads, `vpunpck{l,h}qdq`, `vshufi32x4`, `vmovq` and
`vpbroadcastq` acts on each quadword on its own, so a term is evaluated at a
quadword `k < 8`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj lo32 qword_paddq qword_pmuludq qword_and
  qword_or qword_andn qword_punpcklqdq qword_punpckhqdq qword_psllq qword_psrlq mod2_lt sel4 sel4_lt vec
  vec_gpr vec_mem vec_rd vec_wr vec_trans)

/-! ## Quadwords -/

/-- Quadword `k` (`k < 8`) of `zmm r`. -/
def qz (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.zlane r (k / 2)) (k % 2)

theorem cases8 {k : Nat} (hk : k < 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem div2_lt {k : Nat} (hk : k < 8) : k / 2 < 4 := by omega

/-- The quadwords of the low 256 bits are those of `Avx2.qw`. -/
theorem qz_qw (s : State) (r : XReg) {k : Nat} (hk : k < 4) : qz s r k = Avx2.qw s r k := by
  simp only [qz, Avx2.qw, State.zlane, show k / 2 < 2 by omega, ite_true]

theorem qz_zbin (op : ZBinOp) (s : State) (d a b r : XReg) {k : Nat} (hk : k < 8) :
    qz ((ZOp.zbin op d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.zlane a (k / 2)) (s.zlane b (k / 2))) (k % 2) else qz s r k := by
  simp only [qz, zlane_zbin _ _ _ _ _ _ (div2_lt hk)]
  split <;> rfl

theorem qz_vshift (op : ZShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vshift op d a n).exec s) r k =
      if r = d then qword (op.sse.eval (s.zlane a (k / 2)) n) (k % 2) else qz s r k := by
  simp only [qz, zlane_vshift _ _ _ _ _ _ (div2_lt hk)]
  split <;> rfl

theorem qz_vmovdqa64 (s : State) (d a r : XReg) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vmovdqa64 d a).exec s) r k = if r = d then qz s a k else qz s r k := by
  simp only [qz, zlane_vmovdqa64 _ _ _ _ (div2_lt hk)]
  split <;> rfl

theorem qz_vpbroadcastq (s : State) (d a r : XReg) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vpbroadcastq d a).exec s) r k = if r = d then qz s a 0 else qz s r k := by
  simp only [qz, zlane_vpbroadcastq _ _ _ _ (div2_lt hk)]
  split
  · have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp [State.zlane, State.lane]
  · rfl

theorem sel4_eq (n : BitVec 8) (i : Nat) : (n.extractLsb' (2 * i) 2).toNat = sel4 n.toNat i := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul, sel4]

theorem qz_vshufi32x4 (s : State) (d a b r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vshufi32x4 d a b n).exec s) r k =
      if r = d then (if k / 2 < 2 then qz s a else qz s b) (2 * sel4 n.toNat (k / 2) + k % 2)
      else qz s r k := by
  simp only [qz, zlane_vshufi32x4 _ _ _ _ _ _ (div2_lt hk)]
  split
  · rw [shuf4Lanes_eq, sel4_eq]
    have h1 : (2 * sel4 n.toNat (k / 2) + k % 2) / 2 = sel4 n.toNat (k / 2) := by omega
    have h2 : (2 * sel4 n.toNat (k / 2) + k % 2) % 2 = k % 2 := by omega
    by_cases hl : k / 2 < 2 <;> simp only [hl, ite_true, ite_false, qz, h1, h2]
  · rfl

theorem qz_vmovq (s : State) (d r : XReg) (g : Reg) {k : Nat} (hk : k < 8) :
    qz ((VOp.vmovq d g).exec s) r k = if r = d then (if k = 0 then s.gpr g else 0) else qz s r k := by
  simp only [VOp.exec, qz, State.zlane_setV128 _ _ _ _ _ (div2_lt hk)]
  split
  · rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Nat.zero_div, Nat.zero_mod, ite_true, Avx2.qword_app0]
    · simp only [show 1 / 2 = 0 from rfl, show 1 % 2 = 1 from rfl, ite_true, Avx2.qword_app1]; rfl
    all_goals simp [qword]
  · rfl

theorem qz_load (s : State) (d r : XReg) (a : Addr) {k : Nat} (hk : k < 8) :
    qz (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)) r k =
      if r = d then s.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qz s r k := by
  simp only [qz]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (div2_lt hk),
    pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) (div2_lt hk)]
  split
  · have e : qword ((s.mem.readW a 512).extractLsb' (128 * (k / 2)) 128) (k % 2) =
        (s.mem.readW a 512).extractLsb' (8 * (8 * k)) (8 * 8) := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
        decide_eq_true (show 64 * (k % 2) + j < 128 by omega)]
      exact congrArg _ (by omega)
    rw [e]
    exact readW_extract _ _ (by omega)
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
  /-- `vshufi32x4` with the immediate `sel`. -/
  | shuf (a b : Q) (sel : Nat)
  deriving DecidableEq, Repr

/-- The quadword of `vshufi32x4` with the immediate `sel` that quadword `k`
of the result is: in the first source for the lower two lanes, else the
second. -/
def shufIdx (sel k : Nat) : Nat := 2 * sel4 sel (k / 2) + k % 2

theorem shufIdx_lt (sel k : Nat) : shufIdx sel k < 8 := by
  have := sel4_lt sel (k / 2)
  simp only [shufIdx]; omega

def Q.eval (s₀ : State) : Q → Nat → BitVec 64
  | .reg r, k => qz s₀ (xr r) k
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
  | .shuf a b sel, k => if k / 2 < 2 then a.eval s₀ (shufIdx sel k) else b.eval s₀ (shufIdx sel k)

/-! ## The machine -/

/-- The terms of the vector registers (by number). -/
structure Sym where
  reg : Nat → Q

def Sym.init : Sym := ⟨.reg⟩

def Sym.set (σ : Sym) (d : XReg) (t : Q) : Sym := ⟨fun r => if r = xi d then t else σ.reg r⟩

def Sym.zbin (σ : Sym) (op : ZBinOp) (d a b : XReg) : Option Sym :=
  let A := σ.reg (xi a)
  let B := σ.reg (xi b)
  match op with
  | .vpaddq => some (σ.set d (.add A B))
  | .vpmuludq => some (σ.set d (.mul A B))
  | .vpandq => some (σ.set d (.and A B))
  | .vpandnq => some (σ.set d (.andn A B))
  | .vporq => some (σ.set d (.or A B))
  | .vpunpcklqdq => some (σ.set d (.unpl A B))
  | .vpunpckhqdq => some (σ.set d (.unph A B))
  | _ => none

def Sym.zop (σ : Sym) : ZOp → Option Sym
  | .zbin op d a b => σ.zbin op d a b
  | .vshift op d a n =>
    if n.toNat < 64 then
      match op with
      | .vpsllq => some (σ.set d (.shl (σ.reg (xi a)) n.toNat))
      | .vpsrlq => some (σ.set d (.shr (σ.reg (xi a)) n.toNat))
    else none
  | .vmovdqa64 d a => some (σ.set d (σ.reg (xi a)))
  | .vpbroadcastq d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vshufi32x4 d a b n => some (σ.set d (.shuf (σ.reg (xi a)) (σ.reg (xi b)) n.toNat))
  | _ => none

/-- A load of 64 bytes at `rsi + 8 i` (for `i` 0 or 8). -/
def ldIdx (m : MemOp) : Option Nat :=
  if m.base = .rsi ∧ m.index = none then
    if m.disp = 0 then some 0 else if m.disp = 64 then some 8 else none
  else none

/-- One instruction; loads only if `ld`. -/
def Sym.step (ld : Bool) (σ : Sym) : Instr → Option Sym
  | .zop o => σ.zop o
  | .vop (.vmovq d r) => some (σ.set d (.lane0 (.gpr r)))
  | .vmovdqu32Load d m => if ld then (ldIdx m).map fun i => σ.set d (.ld i) else none
  | _ => none

def Sym.run (ld : Bool) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step ld i).bind fun σ' => σ'.run ld is

/-! ## The machine agrees -/

theorem vec_zop {s₀ s : State} (h : vec s₀ s = s) (o : ZOp) : vec s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> rfl

theorem vec_setV {s₀ s : State} (h : vec s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vec s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem vec_setZ {s₀ s : State} (h : vec s₀ s = s) (d : XReg) (a b c e : BitVec 128) :
    vec s₀ (s.setZ d a b c e) = s.setZ d a b c e := by
  rw [← h]; rfl

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 8 → qz s r k = (σ.reg (xi r)).eval s₀ k
  eq : vec s₀ s = s

theorem SRel.gpr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.gpr = s₀.gpr := vec_gpr h.eq
theorem SRel.mem {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.mem = s₀.mem := vec_mem h.eq
theorem SRel.rd {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.rd = s₀.rd := vec_rd h.eq
theorem SRel.wr {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) : s.wr = s₀.wr := vec_wr h.eq

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, Q.eval, xr_xi], rfl⟩

theorem SRel.set {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {d : XReg} {t : Q} {s' : State}
    (hv : ∀ r k, k < 8 → qz s' r k = if r = d then t.eval s₀ k else qz s r k)
    (he : vec s₀ s' = s') : SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- What the loads may read: 128 bytes at `rsi`. -/
def Ctx (s₀ : State) : Prop :=
  ∀ i, i = 0 ∨ i = 8 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64

theorem ldIdx_ok {m : MemOp} {i : Nat} (h : ldIdx m = some i) :
    (i = 0 ∨ i = 8) ∧ ∀ s : State, s.ea m = s.gpr .rsi + BitVec.ofNat 64 (8 * i) := by
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

theorem hv_of {s s' : State} {d : XReg} {f : Nat → BitVec 64} (hd : ∀ k, k < 8 → qz s' d k = f k)
    (ho : ∀ r, r ≠ d → ∀ k, k < 8 → qz s' r k = qz s r k) :
    ∀ r k, k < 8 → qz s' r k = if r = d then f k else qz s r k := by
  intro r k hk
  by_cases hr : r = d
  · subst hr; rw [ite_eq_left rfl]; exact hd k hk
  · rw [ite_eq_right hr]; exact ho r hr k hk

theorem qz_lane (s : State) (r : XReg) (k : Nat) : qword (s.zlane r (k / 2)) (k % 2) = qz s r k := rfl

theorem sstep_ok {ld : Bool} {s₀ : State} (hc : ld = true → Ctx s₀) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) {i : Instr} (e : σ.step ld i = some σ') : ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 8 → (σ.reg (xi a)).eval s₀ k = qz s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := vec_zop h.eq o
    unfold Sym.zop at e
    split at e
    · rename_i op d a b
      unfold Sym.zbin at e
      split at e <;> cases e <;>
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_right hr]))
          he <;>
        rw [qz_zbin _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZBinOp.sse, Q.eval]
      · rw [qword_paddq _ _ (mod2_lt k), qz_lane, qz_lane, hR a k hk, hR b k hk]
      · rw [qword_pmuludq _ _ (mod2_lt k), qz_lane, qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_and, qz_lane, qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_andn _ _ (mod2_lt k), qz_lane, qz_lane, hR a k hk, hR b k hk]
      · rw [XBinOp.eval, qword_or, qz_lane, qz_lane, hR a k hk, hR b k hk]
      · rw [qword_punpcklqdq _ _ (mod2_lt k)]
        split
        · rename_i h0; rw [hR a k hk, qz, h0]
        · rw [hR b (k - 1) (by omega), qz, show (k - 1) / 2 = k / 2 by omega,
            show (k - 1) % 2 = 0 by omega]
      · rw [qword_punpckhqdq _ _ (mod2_lt k)]
        split
        · rw [hR a (k + 1) (by omega), qz, show (k + 1) / 2 = k / 2 by omega,
            show (k + 1) % 2 = 1 by omega]
        · rw [hR b k hk, qz, show k % 2 = 1 by omega]
    · rename_i op d a n
      split at e
      · rename_i hn
        split at e <;> cases e <;>
          refine h.set (hv_of (fun k hk => ?_)
            (fun r hr k hk => by rw [qz_vshift _ _ _ _ _ _ hk, ite_eq_right hr])) he <;>
          rw [qz_vshift _ _ _ _ _ _ hk, ite_eq_left rfl] <;> simp only [ZShiftOp.sse, Q.eval]
        · rw [qword_psllq _ hn (mod2_lt k), qz_lane, hR a k hk]
        · rw [qword_psrlq _ hn (mod2_lt k), qz_lane, hR a k hk]
      · cases e
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k hk => by rw [qz_vmovdqa64 _ _ _ _ hk, ite_eq_left rfl, hR a k hk])
        (fun r hr k hk => by rw [qz_vmovdqa64 _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qz_vpbroadcastq _ _ _ _ hk, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k hk => by rw [qz_vpbroadcastq _ _ _ _ hk, ite_eq_right hr])) he
    · rename_i d a b n
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, shufIdx]
          split
          · exact (hR a _ (shufIdx_lt _ _)).symm
          · exact (hR b _ (shufIdx_lt _ _)).symm)
        (fun r hr k hk => by rw [qz_vshufi32x4 _ _ _ _ _ _ hk, ite_eq_right hr])) he
    · cases e
  · rename_i d g
    cases e
    refine ⟨(VOp.vmovq d g).exec s, rfl, ?_⟩
    exact h.set (hv_of (fun k hk => by rw [qz_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [Q.eval, h.gpr])
      (fun r hr k hk => by rw [qz_vmovq _ _ _ _ hk, ite_eq_right hr])) (by
        rw [← h.eq]; rfl)
  · rename_i d m
    split at e
    case isFalse => cases e
    rename_i hld
    obtain ⟨i, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hi, hea⟩ := ldIdx_ok hs
    have ea : s.ea m = s₀.gpr .rsi + BitVec.ofNat 64 (8 * i) := by rw [hea, h.gpr]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64 := by
      rw [h.rd, h.wr]; exact hc hld i hi
    let v := s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 512
    refine ⟨s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128), by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [qz_load _ _ _ _ hk, ite_eq_right hr]))
      (vec_setZ h.eq _ _ _ _ _)
    rw [qz_load _ _ _ _ hk, ite_eq_left rfl, h.mem, Offset.add_add]; simp only [Q.eval, Nat.mul_add]
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

end VG.Proof.Poly1305.X86_64.Avx512
