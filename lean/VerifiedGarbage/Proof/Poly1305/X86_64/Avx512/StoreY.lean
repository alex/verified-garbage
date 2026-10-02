import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr

/-!
# Poly1305 on x86-64 with AVX-512: the multipliers into the state

Untrusted: everything here is checked by Lean. `storeY` computes five times
the limbs of `Y` (`fiveY`), stores lane 0 of `Y_i` at `rdi + 56 + 4 i` and of
`5 Y_i` at `rdi + 72 + 4 i` (`1 ≤ i ≤ 4`), each 16-byte store overwriting all
but the first doubleword of the one before, then the mask and the pad bit
at `rdi + 104` and `rdi + 112`. The doubleword at each of these addresses is
then the low doubleword of quadword 0 of the register stored there, which is
all that the loop's `vpmuludq`s read (`MemM`). Everything it writes is
working space of the state (`wR`), below MXCSR's slot at byte 120.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64 (off wR wR_contains sep_off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_keep)

/-! ## `fiveY` -/

def fvS : Sym := (Sym.init.run false fiveY).get (by decide +kernel)
theorem fvS_eq : Sym.init.run false fiveY = some fvS := (Option.some_get _).symm

theorem fvS_shape : (∀ i < 5, fvS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    fvS.reg (xi (yreg i)) = .reg (xi (yreg i))) ∧
    ∀ k < 4, fvS.reg (xi (dreg k)) = .add (.shl (.reg (xi (yreg (k + 1)))) 2) (.reg (xi (yreg (k + 1)))) := by
  decide +kernel

theorem five_lo (y : Nat) : (y * 2 ^ 2 % 2 ^ 64 + y) % 2 ^ 64 % 2 ^ 32 = 5 * (y % 2 ^ 32) % 2 ^ 32 := by
  omega

theorem fiveY_ok (s : State) :
    WP isa (.block fiveY) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k) ∧
      ∀ k < 4, (qz s' (dreg k) 0).toNat % 2 ^ 32 = 5 * yl s 0 (k + 1) % 2 ^ 32 := by
  refine WP.mono (run_ok (fun h => by cases h) fvS_eq) fun s' h => ⟨h.eq, fun i hi k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).2]; simp only [Q.eval, xr_xi]
  · rw [h.natw _ (by decide), fvS_shape.2 k hk]
    simp only [Q.natw, envOf_v, yl]
    exact five_lo _

/-! ## The stores -/

/-- 16-byte stores of `xmm` registers at `rdi + d`. -/
def stores (L : List (Nat × XReg)) : List Instr := L.map fun e => .vmovdquStore .l128 (at_ .rdi e.1) e.2

/-- The memory after `stores L` from `m`, at `p`, with the registers `x`. -/
def wrAll (m : Mem) (p : Addr) (x : XReg → BitVec 128) : List (Nat × XReg) → Mem
  | [] => m
  | e :: L => wrAll (m.writeW (off p e.1) (x e.2)) p x L

theorem stores_ok : ∀ (L : List (Nat × XReg)) (s : State),
    (∀ e ∈ L, InRegions s.wr (off (s.gpr .rdi) e.1) 16) →
    WP isa (.block (stores L)) s fun s' => s' = { s with mem := wrAll s.mem (s.gpr .rdi) s.xmm L }
  | [], s, _ => WP.block_nil rfl
  | e :: L, s, hw => by
    have h₀ := hw e (List.mem_cons_self ..)
    refine WP.block_cons_iff.2 ⟨{ s with mem := s.mem.writeW (off (s.gpr .rdi) e.1) (s.xmm e.2) }, ?_, ?_⟩
    · show s.store128 (off (s.gpr .rdi) e.1) (s.xmm e.2) = _
      simp only [State.store128, h₀, ite_true]
    · exact WP.mono (stores_ok L _ fun e' he => hw e' (List.mem_cons_of_mem _ he)) fun s' h => h

/-- The registers `storeY` stores, at their displacements: `Y_i` at
`56 + 4 i`, and `5 Y_(k+1)` (in `D_k`) at `76 + 4 k`. -/
def stL : List (Nat × XReg) :=
  [(56, yreg 0), (60, yreg 1), (64, yreg 2), (68, yreg 3), (72, yreg 4),
   (76, dreg 0), (80, dreg 1), (84, dreg 2), (88, dreg 3)]

theorem storeY_eq : storeY = fiveY ++ (stores stL ++ ([.store mMask .r8, .store mPad .r9] : List Instr)) := rfl

theorem wrAll_frame {p : Addr} {x : XReg → BitVec 128} :
    ∀ (L : List (Nat × XReg)) {m m' : Mem}, (∀ e ∈ L, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128) →
      Frame [wR p] m m' → Frame [wR p] m (wrAll m' p x L)
  | [], _, _, _, h => h
  | e :: L, _, _, hL, h => by
    have he := hL e (List.mem_cons_self ..)
    exact wrAll_frame L (fun e' h' => hL e' (List.mem_cons_of_mem _ h'))
      (h.writeW (List.mem_singleton_self _) _ (wR_contains p he.1 he.2))

theorem rd_sep (m : Mem) (p : Addr) {w n : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hn : n / 8 ≤ 16) (hk : w / 8 ≤ 16) (h : d + n / 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) n = m.readW (off p d) n :=
  Mem.readW_writeW_sep (sep_off p hd he hn hk h) (by omega)

theorem rd32_self (m : Mem) (p : Addr) (d : Nat) (v : BitVec 128) :
    (m.writeW (off p d) v).readW (off p d) 32 = v.extractLsb' 0 32 := by
  have h := readW_writeW_inside m (off p d) v (k := 0) (n := 4) (by decide) (by decide)
  rwa [show off p d + BitVec.ofNat 64 0 = off p d from BitVec.add_zero _] at h

theorem lo32_rd (m : Mem) (a : Addr) : (m.readW a 64).toNat % 2 ^ 32 = (m.readW a 32).toNat := by
  have h := readW_extract m a (w := 64) (k := 0) (n := 4) (by decide)
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero _] at h
  rw [← h, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- The memory `storeY` leaves. -/
def yMem (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) : Mem :=
  ((wrAll m p x stL).writeW (off p 104) a).writeW (off p 112) b

theorem yMem_lo (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    ∀ e ∈ stL, ((yMem m p x a b).readW (off p e.1) 64).toNat % 2 ^ 32 = ((x e.2).extractLsb' 0 32).toNat := by
  intro e he
  rw [lo32_rd]
  simp only [stL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [yMem, stL, wrAll, rd_sep, rd32_self]

theorem yMem_mask (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 104) 64 = a := by
  rw [yMem, rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem yMem_pad (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 112) 64 = b := by
  rw [yMem, Mem.readW_writeW_self64]

theorem yMem_mx (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 120) 32 = m.readW (off p 120) 32 := by
  simp (disch := omega) only [yMem, stL, wrAll, rd_sep]

theorem yMem_frame (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    Frame [wR p] m (yMem m p x a b) :=
  ((wrAll_frame stL (by decide) (Frame.refl _ _)).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 104) (n := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 112) (n := 8) (by decide) (by decide))

theorem xmm_lo32 (s : State) (r : XReg) : ((s.xmm r).extractLsb' 0 32).toNat = (qz s r 0).toNat % 2 ^ 32 := by
  have e : qz s r 0 = (s.xmm r).extractLsb' 0 64 := rfl
  rw [e, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-- What `storeY` leaves. -/
structure StoreYPost (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  hy : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k
  frame : Frame [wR (s.gpr .rdi)] s.mem s'.mem
  mx : s'.mem.readW (off (s.gpr .rdi) 120) 32 = s.mem.readW (off (s.gpr .rdi) 120) 32
  r : ∀ i < 5, mr s' i = yl s 0 i
  five : ∀ i, 1 ≤ i → i < 5 → ms s' i = 5 * yl s 0 i % 2 ^ 32
  mask : (envOf s').mb 104 = (s.gpr .r8).toNat
  pad : (envOf s').mb 112 = (s.gpr .r9).toNat

theorem storeY_ok (s : State) (hw : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 16)
    (hw8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8) :
    WP isa (.block storeY) s (StoreYPost s) := by
  rw [storeY_eq]
  refine WP.block_append (WP.mono (fiveY_ok s) fun s₁ ⟨v₁, hy₁, f₁⟩ => ?_)
  obtain ⟨g₁, m₁, rd₁, wr₁, mx₁⟩ := vec_keep v₁
  have hw₁ : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 16 := by
    rw [g₁, wr₁]; exact hw
  have hw₁8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 8 := by
    rw [g₁, wr₁]; exact hw8
  refine WP.block_append (WP.mono (stores_ok stL s₁ fun e he => ?_) fun s₂ e₂ => ?_)
  · have b := (show ∀ e ∈ stL, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128 by decide) e he
    exact hw₁ e.1 b.1 b.2
  subst e₂
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 104) (s₁.gpr .r8) = _ by
    simp only [State.store64, hw₁8 104 (by decide) (by decide), ite_true]; rfl), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 112) (s₁.gpr .r9) = _ by
    simp only [State.store64, hw₁8 112 (by decide) (by decide), ite_true]; rfl), WP.block_nil ?_⟩
  show StoreYPost s { s₁ with mem := yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }
  have M : ∀ d, (envOf { s₁ with mem := yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }).mb d =
      ((yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)).readW (off (s₁.gpr .rdi) d) 64).toNat :=
    fun d => rfl
  have L := yMem_lo s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)
  refine ⟨by rw [← g₁], by rw [← rd₁], by rw [← wr₁], by rw [← mx₁], fun i hi k hk => hy₁ i hi k hk, ?_, ?_, fun i hi => ?_, fun i h₁ hi => ?_, ?_, ?_⟩
  · rw [← g₁, ← m₁]; exact yMem_frame _ _ _ _ _
  · rw [← g₁, ← m₁]; exact yMem_mx _ _ _ _ _
  · simp only [mr]
    rw [M]
    rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
    · rw [L (56, yreg 0) (by decide), xmm_lo32, (hy₁ 0 (by decide) 0 (by decide)).2]; rfl
    · rw [L (60, yreg 1) (by decide), xmm_lo32, (hy₁ 1 (by decide) 0 (by decide)).2]; rfl
    · rw [L (64, yreg 2) (by decide), xmm_lo32, (hy₁ 2 (by decide) 0 (by decide)).2]; rfl
    · rw [L (68, yreg 3) (by decide), xmm_lo32, (hy₁ 3 (by decide) 0 (by decide)).2]; rfl
    · rw [L (72, yreg 4) (by decide), xmm_lo32, (hy₁ 4 (by decide) 0 (by decide)).2]; rfl
  · simp only [ms]
    rw [M]
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    · rw [L (76, dreg 0) (by decide), xmm_lo32]; exact f₁ 0 (by decide)
    · rw [L (80, dreg 1) (by decide), xmm_lo32]; exact f₁ 1 (by decide)
    · rw [L (84, dreg 2) (by decide), xmm_lo32]; exact f₁ 2 (by decide)
    · rw [L (88, dreg 3) (by decide), xmm_lo32]; exact f₁ 3 (by decide)
  · rw [M, yMem_mask, g₁]
  · rw [M, yMem_pad, g₁]

end VG.Proof.Poly1305.X86_64.Avx512
