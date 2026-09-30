import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Rounds

/-!
# ChaCha20 on x86-64 with AVX-512: straight-line code, doubleword by doubleword

Untrusted: everything here is checked by Lean. Outside the rounds, every
instruction of the code moves, adds or XORs doublewords of `zmm` registers
and of three regions of memory: the state (at `rdi`), `buf` (at `rcx`) and
1024 bytes of data (at `rsi`). `Sym.run` computes each doubleword after a
block of such instructions as a term (`T`) in the doublewords before it, and
`run_ok` proves the machine agrees; the terms themselves are then compared
by the kernel.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word)

/-- The base register of region `b`: the state, `buf` and the data. -/
def baseR : Nat → Reg
  | 0 => .rdi | 1 => .rcx | _ => .rsi

/-- The doublewords of region `b`. -/
def bsize : Nat → Nat
  | 0 => 16 | 1 => 80 | _ => 256

/-- The doublewords of region `b` that may be written: the saved registers in
`buf`, and the data. -/
def wsize : Nat → Nat
  | 0 => 0 | 1 => 32 | _ => 256

def bidx : Reg → Option Nat
  | .rdi => some 0 | .rcx => some 1 | .rsi => some 2 | _ => none

theorem bidx_some {r : Reg} {b : Nat} (h : bidx r = some b) : r = baseR b ∧ b < 3 := by
  cases r <;> simp only [bidx, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

/-- Region `b`, where the code starts. -/
def regn (s₀ : State) (b : Nat) : Region := ⟨s₀.gpr (baseR b), 4 * bsize b⟩

/-- The regions written. -/
def wregs (s₀ : State) : List Region := [⟨s₀.gpr .rcx, 128⟩, ⟨s₀.gpr .rsi, 1024⟩]

/-- A doubleword, from the doublewords where the code starts. -/
inductive T
  /-- Doubleword `p` of `zmm r`. -/
  | reg (r p : Nat)
  /-- Doubleword `i` of region `b`. -/
  | mem (b i : Nat)
  | add (a b : T)
  | xor (a b : T)
  deriving DecidableEq

def T.eval (s₀ : State) : T → Word
  | .reg r p => zw s₀ (zreg r) p
  | .mem b i => s₀.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32
  | .add a b => a.eval s₀ + b.eval s₀
  | .xor a b => a.eval s₀ ^^^ b.eval s₀

/-- The doublewords of the registers (by `xidx`) and regions, as terms. -/
structure Sym where
  reg : Nat → Nat → T
  mem : Nat → Nat → T
  /-- Whether memory may have been written. -/
  dirty : Bool

def Sym.init : Sym := ⟨.reg, .mem, false⟩

def Sym.setReg (σ : Sym) (d : Nat) (f : Nat → T) : Sym :=
  { σ with reg := fun r p => if r = d then f p else σ.reg r p }

/-- The two-bit field `i` of `o`. -/
def sel2 (o i : Nat) : Nat := o / 4 ^ i % 4

/-- Doubleword `p` of `op a b`. -/
def zbinT (op : ZBinOp) (A B : Nat → T) (p : Nat) : T :=
  match op with
  | .vpaddd => .add (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpxord => .xor (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpunpckldq => if p % 4 % 2 = 0 then A (4 * (p / 4) + p % 4 / 2) else B (4 * (p / 4) + p % 4 / 2)
  | .vpunpckhdq =>
    if p % 4 % 2 = 0 then A (4 * (p / 4) + (2 + p % 4 / 2)) else B (4 * (p / 4) + (2 + p % 4 / 2))
  | .vpunpcklqdq => if p % 4 < 2 then A (4 * (p / 4) + p % 4) else B (4 * (p / 4) + (p % 4 - 2))
  | .vpunpckhqdq => if p % 4 < 2 then A (4 * (p / 4) + (2 + p % 4)) else B (4 * (p / 4) + p % 4)

/-- The region and first doubleword of an access of `n` doublewords, within
the first `lim b` doublewords of its region `b`. -/
def slot (m : MemOp) (n : Nat) (lim : Nat → Nat) : Option (Nat × Nat) :=
  match bidx m.base, m.index, m.disp with
  | some b, none, .ofNat d => if d % 4 = 0 ∧ d / 4 + n ≤ lim b then some (b, d / 4) else none
  | _, _, _ => none

def Sym.step (σ : Sym) : Instr → Option Sym
  | .zop (.zbin op d a b) => some (σ.setReg (xidx d) (zbinT op (σ.reg (xidx a)) (σ.reg (xidx b))))
  | .zop (.vpshufd d a o) =>
    some (σ.setReg (xidx d) fun p => σ.reg (xidx a) (4 * (p / 4) + sel2 o.toNat (p % 4)))
  | .zop (.vshufi32x4 d a b n) =>
    some (σ.setReg (xidx d) fun p =>
      (if p / 4 < 2 then σ.reg (xidx a) else σ.reg (xidx b)) (4 * sel2 n.toNat (p / 4) + p % 4))
  | .vmovdqu32Load d m => (slot m 16 bsize).map fun (b, i) => σ.setReg (xidx d) fun p => σ.mem b (i + p)
  | .vbroadcasti32x4 d m =>
    (slot m 4 bsize).map fun (b, i) => σ.setReg (xidx d) fun p => σ.mem b (i + p % 4)
  | .vmovdqu32Store m r => (slot m 16 wsize).map fun (b, i) =>
    { σ with
      mem := fun b' i' => if b' = b ∧ i ≤ i' ∧ i' < i + 16 then σ.reg (xidx r) (i' - i) else σ.mem b' i'
      dirty := true }
  | _ => none

def Sym.run (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.step i).bind fun σ' => σ'.run is

/-! ## The machine agrees -/

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toInt_eq; simp

theorem add_ofNat' (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem slot_ok {m : MemOp} {n : Nat} {lim : Nat → Nat} {b i : Nat} (h : slot m n lim = some (b, i)) :
    b < 3 ∧ i + n ≤ lim b ∧ ∀ s : State, s.ea m = s.gpr (baseR b) + BitVec.ofNat 64 (4 * i) := by
  unfold slot at h
  split at h
  · rename_i b' d hb hi hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hb3⟩ := bidx_some hb
      refine ⟨hb3, hc.2, fun s => ?_⟩
      simp only [State.ea, hi, hd, ofInt_ofNat, ← e]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1)]
    · cases h
  · cases h

theorem bsize_le (b : Nat) : bsize b ≤ 256 := by
  unfold bsize; split <;> decide

theorem wsize_le (b : Nat) : wsize b ≤ bsize b := by
  unfold wsize bsize; split <;> decide

theorem regn_contains (s₀ : State) {b i n : Nat} (h : i + n ≤ bsize b) :
    (regn s₀ b).Contains ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  have := bsize_le b
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  simp only [regn]; omega

/-- The regions: writable (and so readable) and disjoint. -/
structure Ctx (s₀ : State) : Prop where
  w : ∀ b i n, b < 3 → i + n ≤ bsize b →
    InRegions s₀.wr ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : ∀ b b', b < 3 → b' < 3 → b ≠ b' → (regn s₀ b).Disjoint (regn s₀ b')

/-- The terms `σ` hold in `s`. -/
structure SRel (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 16 → zw s r p = (σ.reg (xidx r) p).eval s₀
  mem : ∀ b i, b < 3 → i < bsize b →
    s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem b i).eval s₀
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (wregs s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

theorem zreg_xidx (r : XReg) : zreg (xidx r) = r := by cases r <;> rfl

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, zreg_xidx], fun _ _ _ _ => rfl, rfl, rfl, rfl,
    Frame.refl _ _, fun _ => rfl⟩

theorem SRel.setReg {σ : Sym} {s₀ s s' : State} (h : SRel σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 16 → zw s' r p = if r = d then (f p).eval s₀ else zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRel (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi => by rw [hm]; exact h.mem b i hb hi, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

/-! ### Lane operations -/

theorem zw_split {s : State} {r : XReg} {p : Nat} : zw s r p = dword (s.zlane r (p / 4)) (p % 4) := rfl

theorem zbinT_eval (op : ZBinOp) {A B : Nat → T} {s₀ : State} {x y : BitVec 128} {p : Nat}
    (hA : ∀ k, k < 4 → (A (4 * (p / 4) + k)).eval s₀ = dword x k)
    (hB : ∀ k, k < 4 → (B (4 * (p / 4) + k)).eval s₀ = dword y k) :
    (zbinT op A B p).eval s₀ = dword (op.sse.eval x y) (p % 4) := by
  have hq : p % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [zbinT]
  generalize p % 4 = q at *
  generalize 4 * (p / 4) = l at *
  have a0 := hA 0 (by decide); have a1 := hA 1 (by decide)
  have a2 := hA 2 (by decide); have a3 := hA 3 (by decide)
  have b0 := hB 0 (by decide); have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide); have b3 := hB 3 (by decide)
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> cases op <;>
    simp only [ZBinOp.sse, T.eval, dword_paddd _ _ (show (0 : Nat) < 4 by decide),
      dword_paddd _ _ (show (1 : Nat) < 4 by decide), dword_paddd _ _ (show (2 : Nat) < 4 by decide),
      dword_paddd _ _ (show (3 : Nat) < 4 by decide), dword_pxor, dword_punpckldq, dword_punpckhdq,
      punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ite_true, ite_false, a0, a1, a2, a3, b0, b1, b2, b3]

theorem zw_lk (s : State) (r : XReg) {l k : Nat} (hk : k < 4) :
    zw s r (4 * l + k) = dword (s.zlane r l) k := by
  simp only [zw_split]; rw [show (4 * l + k) / 4 = l by omega, show (4 * l + k) % 4 = k by omega]

theorem sel2_eq (o : BitVec 8) (i : Nat) : (o.extractLsb' (2 * i) 2).toNat = sel2 o.toNat i := by
  simp only [BitVec.extractLsb'_toNat, sel2, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem sel2_lt (o i : Nat) : sel2 o i < 4 := Nat.mod_lt _ (by decide)

theorem pick4_same (v : BitVec 128) {i : Nat} (hi : i < 4) : pick4 v v v v i = v := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem pick4_ext (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128) l =
      v.extractLsb' (128 * l) 128 := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem dword_read512 (m : Mem) (a : Addr) {p : Nat} (hp : p < 16) :
    dword ((m.readW a 512).extractLsb' (128 * (p / 4)) 128) (p % 4) =
      m.readW (a + BitVec.ofNat 64 (4 * p)) 32 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega), show 128 * (p / 4) + 32 * (p % 4) = 8 * (4 * p) by omega]
  exact readW_extract m a (w := 512) (k := 4 * p) (n := 4) (by omega)

theorem in_regn {s₀ s : State} (hc : Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ bsize b) : InRegions s.wr ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  hw ▸ hc.w b i n hb h

theorem in_regn' {s₀ s : State} (hc : Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ bsize b) : InRegions (s.rd ++ s.wr) ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  let ⟨r, hr, hc'⟩ := in_regn hc hb hw h; ⟨r, List.mem_append_right _ hr, hc'⟩

/-- One instruction. -/
theorem sstep_ok {s₀ : State} (hc : Ctx s₀) {σ σ' : Sym} {s : State} (h : SRel σ s₀ s) {i : Instr}
    (e : σ.step i = some σ') : ∃ s', exec i s = some s' ∧ SRel σ' s₀ s' := by
  unfold Sym.step at e
  split at e
  · rename_i op d a b
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_zbin _ _ _ _ _ _ (div4_lt hp)]
    split
    · exact (zbinT_eval op (fun k hk => (h.reg a _ (by omega)).symm.trans (zw_lk s a hk))
        (fun k hk => (h.reg b _ (by omega)).symm.trans (zw_lk s b hk))).symm
    · rfl
  · rename_i d a o
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vpshufd _ _ _ _ _ (div4_lt hp)]
    split
    · rw [dword_shufDwords _ _ (mod4_lt p), sel2_eq, ← zw_lk s a (sel2_lt _ _)]
      exact h.reg a _ (by have := sel2_lt o.toNat (p % 4); omega)
    · rfl
  · rename_i d a b n
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vshufi32x4 _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [shuf4Lanes_eq, sel2_eq]
      have := sel2_lt n.toNat (p / 4)
      by_cases hl : p / 4 < 2
      · simp only [hl, ite_true]
        rw [← zw_lk s a (mod4_lt p)]; exact h.reg a _ (by omega)
      · simp only [hl, ite_false]
        rw [← zw_lk s b (mod4_lt p)]; exact h.reg b _ (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn' hc hb h.wr hi
    refine ⟨s.setZ d ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 0 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 128 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 256 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 384 128), by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_ext _ (div4_lt hp), dword_read512 _ _ hp, add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn' hc hb h.wr hi
    refine ⟨s.setZ d (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128), by simp only [exec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_same _ (div4_lt hp), dword_readW _ _ (mod4_lt p), add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := mod4_lt p; omega)
    · rfl
  · rename_i m r
    obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have hi' : i + 16 ≤ bsize b := Nat.le_trans hi (wsize_le b)
    have hb0 : b = 1 ∨ b = 2 := by
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
      · simp [wsize] at hi
      · exact .inl e
      · exact .inr e
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := in_regn hc hb h.wr hi'
    refine ⟨s.setMem (s.mem.writeW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
      by simp only [exec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
      fun b' i' hb' hi'' => ?_, by simp [h.gpr], by simp [h.rd], by simp [h.wr], ?_, fun hd => by cases hd⟩⟩
    · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
    · simp only [State.setMem_mem]
      by_cases hx : b' = b ∧ i ≤ i' ∧ i' < i + 16
      · obtain ⟨rfl, h₁, h₂⟩ := hx
        simp only [and_self, h₁, h₂, ite_true]
        rw [show (regn s₀ b').base + BitVec.ofNat 64 (4 * i') =
            (regn s₀ b').base + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (4 * (i' - i)) by
          rw [add_ofNat']; congr 2; omega]
        refine (readW_writeW_inside s.mem _ (s.zmm r) (k := 4 * (i' - i)) (n := 4) (by omega)
          (by decide)).trans ?_
        rw [show 8 * (4 * (i' - i)) = 8 * (16 * ((i' - i) / 4) + 4 * ((i' - i) % 4)) by omega,
          State.zmm_extract _ _ (by omega) (mod4_lt _), ← zw_split]
        exact h.reg r _ (by omega)
      · rw [ite_eq_right hx]
        by_cases e : b' = b
        · subst e
          have hx' : i' + 1 ≤ i ∨ i + 16 ≤ i' := by omega
          have := bsize_le b'
          exact (readW_writeW_off s.mem _ (s.zmm r) (d := 4 * i') (e := 4 * i) (n := 4)
            (by omega) (by omega) (by omega)).trans (h.mem b' i' hb' hi'')
        · have f := (Frame.refl [regn s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
            (regn_contains s₀ (n := 16) hi')
          rw [f.readW (r := regn s₀ b') (regn_contains s₀ (n := 1) (by omega))
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
            (by decide)]
          exact h.mem b' i' hb' hi''
    · simp only [State.setMem_mem]
      refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .rcx, 128⟩ else ⟨s₀.gpr .rsi, 1024⟩)
        (by rcases hb0 with rfl | rfl <;> simp [wregs]) _ ?_
      rcases hb0 with rfl | rfl
      · simp only [regn, baseR, Region.Contains, ite_true]
        simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
      · simp only [regn, baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
        simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
  · cases e

/-- A block of instructions. -/
theorem srun_ok {s₀ : State} (hc : Ctx s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.run is = some σ' →
      WP isa (.block is) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

end VG.Proof.ChaCha20.X86_64.Avx512
