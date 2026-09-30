import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintBase
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_pack`

Untrusted: everything here is checked by Lean. The code follows the fold
form of `HintBitPack` (`Pack/Hint.lean`, `hpS` and `hpT` of
`Pack/Hint2.lean`) step by step: the bytes of `y` are the array of the spec,
and `eax` its index, which stays below `ω` because it counts the 1s before
the current coefficient (`hpT_idx_lt`).

Constant time but for the hint: the invariants state every register the
code branches on or addresses memory with as a function of the entry state
`s₀`, through the hint, which two runs with the same public data and leak
agree on (`PPub`); so the branches (`Piece.ite`) and the addresses (the
taint analysis, `Piece.taint`) agree.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_eq)
open VG.Proof.MlDsa.Pack

namespace Pk

section
variable (s₀ : State)
/-- `hlen`, `len`, `k`. -/
abbrev hL : Nat := (arg s₀ 1).toNat
abbrev yL : Nat := (arg s₀ 4).toNat
abbrev K : Nat := yL s₀ - ω s₀
/-- `y`. -/
abbrev yR : Region := ⟨wA s₀, yL s₀⟩
/-- The hint. -/
abbrev H : List (Vector Bool n) := hintAt s₀.mem (rA s₀) (K s₀)
/-- The spec's state after `i` polynomials, and `j` coefficients. -/
abbrev S (i : Nat) : Array Byte × Nat := hpS (ω s₀) (K s₀) (H s₀) i
abbrev T (i j : Nat) : Array Byte × Nat := hpT (ω s₀) (K s₀) (H s₀) i j
/-- Coefficient `j` of polynomial `i`. -/
abbrev bit (i j : Nat) : Bool := ((H s₀).getD i noHint)[j]!
end

structure Pre (s₀ : State) : Prop extends Lay s₀ (hL s₀ * 4) (yL s₀) where
  par : (ω s₀, K s₀) ∈ hintParams
  le : ω s₀ ≤ yL s₀
  hlen : hL s₀ = 256 * K s₀
  ones : hintOnes (H s₀) ≤ ω s₀

theorem Pre.of {s₀ : State} (h : (hintBitPackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩

theorem Pre.facts {s₀ : State} (hp : Pre s₀) :
    4 ≤ K s₀ ∧ K s₀ ≤ 8 ∧ ω s₀ ≤ 80 ∧ ω s₀ + K s₀ = yL s₀ ∧ hL s₀ = 256 * K s₀ := by
  have := mem_hintParams hp.par
  have := hp.le
  have := hp.hlen
  have e : K s₀ = yL s₀ - ω s₀ := rfl
  omega

/-- The public data: `esp`, the arguments and the hint. -/
structure Pub (s₀ s₀' : State) : Prop where
  e0 : E0 s₀ = E0 s₀'
  a0 : arg s₀ 0 = arg s₀' 0
  a1 : arg s₀ 1 = arg s₀' 1
  a2 : arg s₀ 2 = arg s₀' 2
  a3 : arg s₀ 3 = arg s₀' 3
  a4 : arg s₀ 4 = arg s₀' 4
  h : H s₀ = H s₀'

theorem Pub.of {s₀ s₀' : State} (hp : Pre s₀) (h : (hintBitPackContract X86.abi 16).pub s₀ s₀') : Pub s₀ s₀' := by
  sig_pub [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e, hl, a0, a1, a2, a3, a4⟩ := h
  refine ⟨e, a0, a1, a2, a3, a4, ?_⟩
  rw [← a0, ← a1] at hl
  have hw := coeffAt_of_leak hl
  simp only [H, K, yL, ω, rA, ← a0, ← a2, ← a4]
  exact hintAt_congr fun t ht => hw t (by have := hp.hlen; simp only [hL, K, yL, ω] at this; omega)

theorem Pub.eK {s₀ s₀' : State} (h : Pub s₀ s₀') : K s₀ = K s₀' := by
  show (arg s₀ 4).toNat - (arg s₀ 2).toNat = (arg s₀' 4).toNat - (arg s₀' 2).toNat; rw [h.a2, h.a4]
theorem Pub.eω {s₀ s₀' : State} (h : Pub s₀ s₀') : ω s₀ = ω s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [h.a2]
theorem Pub.eT {s₀ s₀' : State} (h : Pub s₀ s₀') (i j : Nat) : T s₀ i j = T s₀' i j := by
  show hpT (ω s₀) (K s₀) (H s₀) i j = hpT (ω s₀') (K s₀') (H s₀') i j; rw [h.h, h.eω, h.eK]
theorem Pub.eS {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : S s₀ i = S s₀' i := by
  show hpS (ω s₀) (K s₀) (H s₀) i = hpS (ω s₀') (K s₀') (H s₀') i; rw [h.h, h.eω, h.eK]

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [yR s₀] (P0 s₀).mem s.mem

theorem Base.keep {s₀ s s' : State} (h : Base s₀ s) {rs : List Reg} (k : Keep rs s s') (hsp : Reg.esp ∉ rs)
    (hm : Frame [yR s₀] s.mem s'.mem) : Base s₀ s' :=
  ⟨(k.gpr hsp).trans h.esp, k.2.1.trans h.rd, k.2.2.trans h.wr, h.frame.trans hm⟩

namespace Base
variable {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s)
include hp h

theorem argw {i : Nat} (hi : i < 5) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [h.frame.readW (arg_contains (n := 5) hi hp.sp') (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.w_g.symm) (by decide)]
  exact hp.P0_argw hi

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := hp.argIn h.rd h.wr hi

/-- A word of the hint, as on entry. -/
theorem word {t : Nat} (ht : t < 256 * K s₀) : coeffAt s.mem (rA s₀) t = coeffAt s₀.mem (rA s₀) t := by
  have := hp.facts
  have hf := hp.r_fit
  have hc : (⟨rA s₀, hL s₀ * 4⟩ : Region).Contains (coeffAddr (rA s₀) t) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  rw [coeffAt_eq, coeffAt_eq, h.frame.readW hc (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.r_w) (by decide),
    hp.P0_keep.readW hc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← hp.stk_eq]; exact hp.stk_r.symm) (by decide)]

theorem inH {t : Nat} (ht : t < 256 * K s₀) : InRegions (s.rd ++ s.wr) (coeffAddr (rA s₀) t) 4 := by
  have := hp.facts
  have hf := hp.r_fit
  rw [h.rd, h.wr, pushed_rd, hp.rd]
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩

theorem inY {t : Nat} (ht : t < yL s₀) : InRegions s.wr (wA s₀ + BitVec.ofNat 64 t) 1 := by
  have hf := hp.w_fit
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨yR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩

end Base

/-- A byte of `y`. -/
theorem yAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < yL s₀) :
    addr (arg s₀ 3 + BitVec.ofNat 32 t) 0 = wA s₀ + BitVec.ofNat 64 t := by
  have := hp.w_fit; rw [addr_add (by omega), Nat.add_zero]

/-- A word of the hint. -/
theorem hAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 256 * K s₀) :
    addr (arg s₀ 0 + BitVec.ofNat 32 (4 * t)) 0 = coeffAddr (rA s₀) t := by
  have := hp.facts; have := hp.r_fit; rw [addr_add (by omega), Nat.add_zero]

theorem bit_eq {s₀ : State} {i j : Nat} (hi : i < K s₀) (hj : j < 256) :
    bit s₀ i j = decide (coeffAt s₀.mem (rA s₀) (256 * i + j) ≠ 0) := hintAt_get hi hj

/-! ## Zeroing `y` -/

/-- After `t` bytes. -/
structure ZI (s₀ : State) (t : Nat) (s : State) : Prop extends Base s₀ s where
  edi : s.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 t
  ecx : s.gpr .ecx = BitVec.ofNat 32 (yL s₀ - t)
  eax : s.gpr .eax = 0
  zero : ∀ u < t, s.mem (wA s₀ + BitVec.ofNat 64 u) = 0

theorem zinit_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (ZI · 0) (.block hbpZeroInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have b₀ : Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a3 : addr ((P0 s₀).gpr .esp) 32 = argAddr s₀ 3 := argEa rfl 3
    have a4 : addr ((P0 s₀).gpr .esp) 36 = argAddr s₀ 4 := argEa rfl 4
    have i3 := b₀.argIn hp (i := 3) (by omega)
    have i4 := b₀.argIn hp (i := 4) (by omega)
    have v3 := b₀.argw hp (i := 3) (by omega)
    have v4 := b₀.argw hp (i := 4) (by omega)
    have hb : WP isa (.block hbpZeroInit) (P0 s₀) fun s' => s'.gpr .edi = arg s₀ 3 ∧ s'.gpr .ecx = arg s₀ 4 ∧
        s'.gpr .eax = 0 ∧ s'.mem = (P0 s₀).mem := by
      hrun [hbpZeroInit, a3, a4, i3, i4, v3, v4]
    refine (WP.keep [.edi, .ecx, .eax] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨b₀.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e1]; simp, by rw [e2]; simp, e3,
        fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.e0]

theorem zstep {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < yL s₀) {s : State} (h : ZI s₀ t s) :
    WP isa (.block hbpZeroBody) s fun s' => ZI s₀ (t + 1) s' ∧ isa.eval .ne s' = some (decide (t + 1 < yL s₀)) := by
  have hf := hp.w_fit
  have := hp.facts
  have ea := yAddr hp ht
  have hin := h.inY hp ht
  have hb : WP isa (.block hbpZeroBody) s fun s' => s'.gpr .edi = s.gpr .edi + 1 ∧ s'.gpr .ecx = s.gpr .ecx - 1 ∧
      s'.zf = some (s.gpr .ecx - 1 == 0) ∧
      s'.mem = s.mem.writeW (wA s₀ + BitVec.ofNat 64 t) (BitVec.setWidth 8 (0 : BitVec 32)) := by
    hrun [hbpZeroBody, h.edi, ea, hin, h.eax]
  have hc : (yR s₀).Contains (wA s₀ + BitVec.ofNat 64 t) (8 / 8) := Offset.contains_base _ (by omega) (by omega)
  refine (WP.keep [.edi, .ecx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ => ?_
  have hm : Frame [yR s₀] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  refine ⟨⟨h.keep k (by decide) hm, by rw [e1, h.edi, add_one'], by rw [e2, h.ecx]; exact cnt_next ht,
      by rw [k.gpr (by decide), h.eax], fun u hu => ?_⟩, eval_ne_cnt ht (by omega) (by rw [z, h.ecx])⟩
  rw [m, VG.WriteBytes.writeW8_apply]
  split
  · rfl
  · rename_i hne
    exact h.zero u (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hu) fun e => hne (by rw [e]))

theorem zloop_piece : Piece Pre Pub (ZI · 0) (fun s₀ s => ZI s₀ (yL s₀) s) (.loop (.block hbpZeroBody) .ne) :=
  countLoopN (fun t s₀ s => ZI s₀ t s) yL (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => by simp only [yL, hq.a4]) [.edi] (fun t s₀ s hp h ht => zstep hp ht h)
    (fun t s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.a3]) (by taint_decide)

/-! ## The polynomials -/

/-- Within polynomial `i`: the registers of coefficient `j`, and the data
after `d` coefficients. -/
structure CI (s₀ : State) (i j d : Nat) (s : State) : Prop extends Base s₀ s where
  lt : i < K s₀
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * (256 * i + j))
  ebx : s.gpr .ebx = BitVec.ofNat 32 j
  eax : s.gpr .eax = BitVec.ofNat 32 (T s₀ i d).2
  edi : s.gpr .edi = arg s₀ 3
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (ω s₀ + i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (K s₀ - i)
  y : bytesAt s.mem (wA s₀) (yL s₀) = (T s₀ i d).1.toList

/-- `CI`, after a block that writes only `edx` and the flags. -/
theorem CI.edx {s₀ s s' : State} {i j d : Nat} (h : CI s₀ i j d s) (k : Keep [.edx] s s') (hm : s'.mem = s.mem) :
    CI s₀ i j d s' :=
  ⟨h.keep k (by decide) (by rw [hm]; exact Frame.refl _ _), h.lt, by rw [k.gpr (by decide), h.esi],
    by rw [k.gpr (by decide), h.ebx], by rw [k.gpr (by decide), h.eax], by rw [k.gpr (by decide), h.edi],
    by rw [k.gpr (by decide), h.ecx], by rw [k.gpr (by decide), h.ebp], by rw [hm, h.y]⟩

/-- Before polynomial `i`. -/
structure PI (s₀ : State) (i : Nat) (s : State) : Prop extends Base s₀ s where
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * (256 * i))
  eax : s.gpr .eax = BitVec.ofNat 32 (S s₀ i).2
  edi : s.gpr .edi = arg s₀ 3
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (ω s₀ + i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (K s₀ - i)
  y : bytesAt s.mem (wA s₀) (yL s₀) = (S s₀ i).1.toList

theorem setup_piece : Piece Pre Pub (fun s₀ s => ZI s₀ (yL s₀) s) (PI · 0) (.block hbpSetup) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a0 : addr (s.gpr .esp) 20 = argAddr s₀ 0 := argEa h.esp 0
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have a3 : addr (s.gpr .esp) 32 = argAddr s₀ 3 := argEa h.esp 3
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i0 := h.argIn hp (i := 0) (by omega)
    have i2 := h.argIn hp (i := 2) (by omega)
    have i3 := h.argIn hp (i := 3) (by omega)
    have i4 := h.argIn hp (i := 4) (by omega)
    have v0 := h.argw hp (i := 0) (by omega)
    have v2 := h.argw hp (i := 2) (by omega)
    have v3 := h.argw hp (i := 3) (by omega)
    have v4 := h.argw hp (i := 4) (by omega)
    have hb : WP isa (.block hbpSetup) s fun s' => s'.gpr .esi = arg s₀ 0 ∧ s'.gpr .edi = arg s₀ 3 ∧
        s'.gpr .ecx = arg s₀ 3 + arg s₀ 2 ∧ s'.gpr .ebp = arg s₀ 4 - arg s₀ 2 ∧ s'.mem = s.mem := by
      hrun [hbpSetup, a0, a2, a3, a4, i0, i2, i3, i4, v0, v2, v3, v4]
    have hf := hp.facts
    have l2 := (arg s₀ 2).isLt
    have l4 := (arg s₀ 4).isLt
    refine (WP.keep [.esi, .edi, .ecx, .ebp] hb (by decide)).mono fun s' ⟨⟨e0, e3, ec, eb, m⟩, k⟩ =>
      ⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e0]; simp, ?_, e3, ?_, ?_, ?_⟩
    · rw [k.gpr (by decide), h.eax]; rfl
    · rw [ec]; simp
    · rw [eb]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [K, yL, ω] at hf ⊢
      omega
    · rw [m]
      refine bytesAt_eq (by simp [S, hpS_zero]; omega) fun u hu => ?_
      rw [h.zero u hu]
      simp [S, hpS_zero]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem b0_piece (i : Nat) : Piece Pre Pub (fun s₀ s => PI s₀ i s ∧ i < K s₀) (fun s₀ s => CI s₀ i 0 0 s)
    (.block [.mov .ebx (.imm 0)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block [.mov .ebx (.imm 0)]) s fun s' => s'.gpr .ebx = 0 ∧ s'.mem = s.mem := by hrun
  exact (WP.keep [.ebx] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
    ⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), hi, by rw [k.gpr (by decide), h.esi]; rfl, by rw [e]; rfl,
      by rw [k.gpr (by decide), h.eax]; rfl, by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.ecx],
      by rw [k.gpr (by decide), h.ebp], by rw [m, h.y]; rfl⟩

theorem ne_zero_eq (v : BitVec 32) : (!(v == 0)) = decide (v ≠ 0) := by
  by_cases hv : v = 0 <;> simp [hv, Bool.beq_eq_decide_eq]

theorem load_piece (i j : Nat) : Piece Pre Pub (fun s₀ s => CI s₀ i j j s ∧ j < 256)
    (fun s₀ s => (CI s₀ i j j s ∧ j < 256) ∧ isa.eval .ne s = some (bit s₀ i j)) (.block hbpLoad) := by
  refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hj⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have hf := hp.facts
    have ht : 256 * i + j < 256 * K s₀ := by have := h.lt; omega
    have ea : addr (s.gpr .esi) 0 = coeffAddr (rA s₀) (256 * i + j) := by rw [h.esi]; exact hAddr hp ht
    have hin := h.inH hp ht
    have hb : WP isa (.block hbpLoad) s fun s' =>
        s'.zf = some (s.mem.readW (coeffAddr (rA s₀) (256 * i + j)) 32 == 0) ∧ s'.mem = s.mem := by
      hrun [hbpLoad, ea, hin]
    refine (WP.keep [.edx] hb (by decide)).mono fun s' ⟨⟨z, m⟩, k⟩ => ⟨⟨h.edx k m, hj⟩, ?_⟩
    show s'.zf.map (!·) = _
    rw [z, ← coeffAt_eq, h.word hp ht, bit_eq h.lt hj]
    simp only [Option.map_some, ne_zero_eq]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esi, h'.esi, hq.a0]

theorem set_piece (i j : Nat) : Piece Pre Pub (fun s₀ s => ((CI s₀ i j j s ∧ j < 256) ∧
      isa.eval .ne s = some (bit s₀ i j)) ∧ bit s₀ i j = true) (fun s₀ s => CI s₀ i j (j + 1) s ∧ j < 256)
    (.block hbpSet) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp ⟨⟨⟨h, hj⟩, _⟩, h1⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _⟩, _⟩, _⟩ ⟨⟨⟨h', _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hw := hp.w_fit
    have hlt : (T s₀ i j).2 < ω s₀ :=
      hpT_idx_lt (hintAt_length _ _ _) hp.ones h.lt (show j < n from hj) h1
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = wA s₀ + BitVec.ofNat 64 (T s₀ i j).2 := by
      rw [h.edi, h.eax]; exact yAddr hp (by omega)
    have hin := h.inY hp (t := (T s₀ i j).2) (by omega)
    have hb : WP isa (.block hbpSet) s fun s' => s'.gpr .eax = s.gpr .eax + 1 ∧
        s'.mem = s.mem.writeW (wA s₀ + BitVec.ofNat 64 (T s₀ i j).2) (BitVec.setWidth 8 (s.gpr .ebx)) := by
      hrun [hbpSet, ea, hin]
    have hT : T s₀ i (j + 1) = ((T s₀ i j).1.set! (T s₀ i j).2 (BitVec.ofNat 8 j), (T s₀ i j).2 + 1) := by
      show hpT _ _ _ i (j + 1) = _
      have h1' : ((H s₀).getD i noHint)[j]! = true := h1
      rw [hpT_succ, hpStep, h1']; rfl
    refine (WP.keep [.edx, .eax] hb (by decide)).mono fun s' ⟨⟨ea', m⟩, k⟩ => ⟨⟨h.keep k (by decide) ?_, h.lt,
      by rw [k.gpr (by decide), h.esi], by rw [k.gpr (by decide), h.ebx], ?_, by rw [k.gpr (by decide), h.edi],
      by rw [k.gpr (by decide), h.ecx], by rw [k.gpr (by decide), h.ebp], ?_⟩, hj⟩
    · rw [m]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [ea', h.eax, hT, ofNat_add_one]
    · rw [m, bytesAt_writeW8 _ _ (by omega) (by omega), h.y, hT, h.ebx, b8_eq, toNat_ofNat32 (by omega),
        Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.edi, h'.edi, hq.a3]
    · rw [h.eax, h'.eax, hq.eT]

theorem skip_piece (i j : Nat) : Piece Pre Pub (fun s₀ s => ((CI s₀ i j j s ∧ j < 256) ∧
      isa.eval .ne s = some (bit s₀ i j)) ∧ bit s₀ i j = false) (fun s₀ s => CI s₀ i j (j + 1) s ∧ j < 256)
    (.block []) :=
  nil_piece fun s₀ s _ ⟨⟨⟨h, hj⟩, _⟩, h0⟩ => by
    have hT : T s₀ i (j + 1) = T s₀ i j := by
      show hpT _ _ _ i (j + 1) = _
      have h0' : ((H s₀).getD i noHint)[j]! = false := h0
      rw [hpT_succ, hpStep, h0']; rfl
    exact ⟨⟨h.toBase, h.lt, h.esi, h.ebx, by rw [hT]; exact h.eax, h.edi, h.ecx, h.ebp, by rw [hT]; exact h.y⟩, hj⟩

theorem cmp256 {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 32 (j + 1) - 256 == 0) = decide (j + 1 = 256) := by
  rw [sub_beq_zero, toNat_ofNat32 (by omega)]; rfl

theorem next_piece (i j : Nat) : Piece Pre Pub (fun s₀ s => CI s₀ i j (j + 1) s ∧ j < 256)
    (fun s₀ s => CI s₀ i (j + 1) (j + 1) s ∧ isa.eval .ne s = some (decide (j + 1 < 256))) (.block hbpNext) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hj⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block hbpNext) s fun s' => s'.gpr .esi = s.gpr .esi + 4 ∧ s'.gpr .ebx = s.gpr .ebx + 1 ∧
      s'.zf = some (s.gpr .ebx + 1 - 256 == 0) ∧ s'.mem = s.mem := by hrun [hbpNext]
  refine (WP.keep [.esi, .ebx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ =>
    ⟨⟨h.keep k (by decide) (by rw [m]; exact Frame.refl _ _), h.lt, ?_, by rw [e2, h.ebx, ofNat_add_one],
      by rw [k.gpr (by decide), h.eax], by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.ecx],
      by rw [k.gpr (by decide), h.ebp], by rw [m, h.y]⟩, ?_⟩
  · rw [e1, h.esi, add_four']; congr 2
  · show s'.zf.map (!·) = _
    rw [z, h.ebx, ofNat_add_one, cmp256 hj]
    by_cases e : j + 1 = 256
    · simp [e]
    · simp only [e, decide_false, Option.map_some, Bool.not_false, Option.some.injEq]
      exact (decide_eq_true (by omega)).symm

theorem coef_piece (i j : Nat) : Piece Pre Pub (fun s₀ s => CI s₀ i j j s ∧ j < 256)
    (fun s₀ s => CI s₀ i (j + 1) (j + 1) s ∧ isa.eval .ne s = some (decide (j + 1 < 256))) hbpCoef :=
  Piece.seq (load_piece i j) <| Piece.seq (Piece.ite (fun s₀ => bit s₀ i j) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by show ((H s₀).getD i noHint)[j]! = ((H s₀').getD i noHint)[j]!; rw [hq.h])
    (set_piece i j) (skip_piece i j)) (next_piece i j)

theorem end_piece (i : Nat) : Piece Pre Pub (fun s₀ s => CI s₀ i 256 256 s)
    (fun s₀ s => PI s₀ (i + 1) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀))) (.block hbpEnd) := by
  refine Piece.taint [.ecx] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hw := hp.w_fit
    have hi := h.lt
    have ea : addr (s.gpr .ecx) 0 = wA s₀ + BitVec.ofNat 64 (ω s₀ + i) := by rw [h.ecx]; exact yAddr hp (by omega)
    have hin := h.inY hp (t := ω s₀ + i) (by omega)
    have hb : WP isa (.block hbpEnd) s fun s' => s'.gpr .ecx = s.gpr .ecx + 1 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
        s'.zf = some (s.gpr .ebp - 1 == 0) ∧
        s'.mem = s.mem.writeW (wA s₀ + BitVec.ofNat 64 (ω s₀ + i)) (BitVec.setWidth 8 (s.gpr .eax)) := by
      hrun [hbpEnd, ea, hin]
    have hle : (T s₀ i 256).2 ≤ ω s₀ := hpT_idx_le (hintAt_length _ _ _) hp.ones hi
    have hS : S s₀ (i + 1) = ((T s₀ i n).1.set! (ω s₀ + i) (BitVec.ofNat 8 (T s₀ i n).2), (T s₀ i n).2) :=
      hpS_succ _ _ _ i
    refine (WP.keep [.ecx, .ebp] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ =>
      ⟨⟨h.keep k (by decide) ?_, ?_, ?_, by rw [k.gpr (by decide), h.edi], ?_, ?_, ?_⟩,
        eval_ne_cnt hi (by omega) (by rw [z, h.ebp])⟩
    · rw [m]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [k.gpr (by decide), h.esi]; congr 2
    · rw [k.gpr (by decide), h.eax, hS]
    · rw [e1, h.ecx, add_one']; rfl
    · rw [e2, h.ebp]; exact cnt_next hi
    · rw [m, bytesAt_writeW8 _ _ (by omega) (by omega), h.y, hS, h.eax, b8_eq, toNat_ofNat32 (by omega),
        Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.ecx, h'.ecx, hq.a3, hq.eω]

theorem poly_piece (i : Nat) : Piece Pre Pub (fun s₀ s => PI s₀ i s ∧ i < K s₀)
    (fun s₀ s => PI s₀ (i + 1) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀))) hbpPoly :=
  Piece.seq (b0_piece i) <| Piece.seq (loopN (fun j s₀ s => CI s₀ i j j s) (fun _ => 256) (fun _ _ => by decide)
    (fun _ _ _ _ _ => rfl) (coef_piece i)) (end_piece i)

theorem main_piece : Piece Pre Pub (PI · 0) (fun s₀ s => PI s₀ (K s₀) s) (.loop hbpPoly .ne) :=
  loopN (fun i s₀ s => PI s₀ i s) K (fun s₀ hp => by have := hp.facts; omega) (fun _ _ _ _ hq => hq.eK)
    poly_piece

/-! ## The function -/

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LeafEnd s₀ [yR s₀] s ∧ PI s₀ (K s₀) s)
    (.seq (.block hbpZeroInit) (.seq (.loop (.block hbpZeroBody) .ne) (.seq (.block hbpSetup) (.loop hbpPoly .ne)))) :=
  (Piece.seq zinit_piece <| Piece.seq zloop_piece <| Piece.seq setup_piece main_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (PI s₀ (K s₀)) s₀ s')
    Impl.MlDsa.X86.Pack.hintBitPack :=
  Piece.leaf (fun s₀ => [yR s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩) (fun _ hp => hp.wW) (fun _ _ _ _ hq => hq.e0) body_piece

end Pk

/-- Memory with the arguments `0`, `1024`, `80`, `0x2000` and `84` at `0x5004`. -/
def packSatMem : Mem := fun a =>
  if a = 0x5009 then 4 else if a = 0x500c then 80 else if a = 0x5011 then 0x20 else if a = 0x5014 then 84 else 0

theorem packSat_hint : ∀ t < 256 * 4, coeffAt packSatMem 0 t = 0 := by
  intro t ht
  rw [coeffAt_eq, Mem.readW_congr (m' := fun _ => 0) fun i hi => ?_, ← coeffAt_eq, coeffAt_zero]
  have hlt : (coeffAddr 0 t + BitVec.ofNat 64 i).toNat < 0x1000 := by
    show (0 + BitVec.ofNat 64 (4 * t) + BitVec.ofNat 64 i).toNat < 0x1000
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show BitVec.toNat (0 : Addr) = 0 from rfl]
    omega
  generalize coeffAddr 0 t + BitVec.ofNat 64 i = a at hlt
  simp only [packSatMem]
  split_ifs with h1 h2 h3 h4 <;> first
    | rfl
    | (subst_vars; exact absurd hlt (by decide))

theorem hintBitPack_verified :
    Verified X86.target Impl.MlDsa.X86.Pack.hintBitPack (hintBitPackContract X86.abi 16) := by
  refine Piece.verified ((Pk.piece.pre_mono (fun _ h => Pk.Pre.of h)
    fun s s' h _ hq => Pk.Pub.of (Pk.Pre.of h) hq).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.y.trans (hintBitPack_hpS _ _ _).symm
  · let st := satState packSatMem [⟨0, 4096⟩] [⟨0x2000, 84⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 1024 := by decide
    have a2 : arg st 2 = 80 := by decide
    have a3 : arg st 3 = 0x2000 := by decide
    have a4 : arg st 4 = 84 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide, ?_⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (rw [hintOnes_of_zero fun t ht => by
          rw [show BitVec.setWidth 64 (0 : BitVec 32) = 0 from rfl]
          exact packSat_hint t (by simp at ht; omega)]
         exact Nat.zero_le _)

end VG.Proof.MlDsa.X86.Pack.Hint
