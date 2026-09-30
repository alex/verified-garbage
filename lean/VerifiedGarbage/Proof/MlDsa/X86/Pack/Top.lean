import VerifiedGarbage.Proof.MlDsa.X86.Pack.Loop

/-!
# ML-DSA on x86 (32-bit): the encodings' leaves, loading and branching

Untrusted: everything here is checked by Lean. Each of the encodings is a
leaf with one input and one output buffer, and its arguments on the stack
(`Lay`: what the shared contract says of them on x86). After the leaf's
push, it loads its input pointer (argument `i`) into `esi`, its output
pointer (argument `o`) into `edi`, and its width (argument `w`) into `eax`
(`ldArgs_piece`, `ldPtrs_piece`), and branches on the width (`sel_piece`)
to one of the loops of `Loop.lean`. The branches depend only on the width,
which is public.
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.taint Piece.seq Piece.ite P0 E0 P0_esp P0_wr frameR retR LeafEnd
  P0_argAddr P0_argIn P0_arg saveRegs_len sub_beq_zero toNat_ofNat32)
open VG.Spec.MlDsa (coeffAt)
open VG.Impl.MlKem.X86 (saveRegs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

section
variable (k : Nat) (iP oP : State → BitVec 32) (iL oL : State → Nat)

/-- The stack the leaf's frame uses, as the contract states it. -/
abbrev stkR (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The `k` arguments. -/
abbrev argR (s₀ : State) : Region := ⟨argAddr s₀ 0, 4 * k⟩
/-- The input buffer. -/
abbrev inR (s₀ : State) : Region := ⟨iA iP s₀, iL s₀⟩
/-- The output buffer. -/
abbrev outR (s₀ : State) : Region := ⟨oA oP s₀, oL s₀⟩

/-- A leaf of `k` arguments that reads the input buffer and writes the
output buffer, as the shared contracts lay them out on x86. -/
structure Lay (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * k ≤ 2 ^ 32
  rd : s₀.rd = [inR iP iL s₀]
  wr : s₀.wr = [outR oP oL s₀, argR k s₀]
  i_o : (inR iP iL s₀).Disjoint (outR oP oL s₀)
  i_a : (inR iP iL s₀).Disjoint (argR k s₀)
  o_a : (outR oP oL s₀).Disjoint (argR k s₀)
  ret_i : (retR s₀).Disjoint (inR iP iL s₀)
  ret_o : (retR s₀).Disjoint (outR oP oL s₀)
  ret_a : (retR s₀).Disjoint (argR k s₀)
  stk_i : (stkR s₀).Disjoint (inR iP iL s₀)
  stk_o : (stkR s₀).Disjoint (outR oP oL s₀)
  stk_a : (stkR s₀).Disjoint (argR k s₀)
  i_fit : (iP s₀).toNat + iL s₀ ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + oL s₀ ≤ 2 ^ 32

end

namespace Lay

variable {k : Nat} {iP oP : State → BitVec 32} {iL oL : State → Nat} {s₀ : State}
  (hp : Lay k iP oP iL oL s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem P0_rd : (P0 s₀).rd = [inR iP iL s₀] := by rw [pushed_rd, hp.rd]

theorem P0_wr' : (P0 s₀).wr = frameR s₀ :: [outR oP oL s₀, argR k s₀] := by rw [P0_wr, hp.wr]

theorem push_frame : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rwa [saveRegs_len] at hf

/-- The input buffer is as on entry after the push. -/
theorem in_frame : ∀ r ∈ [frameR s₀], (inR iP iL s₀).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]; rw [← hp.stk_eq]; exact hp.stk_i.symm

/-- The coefficients of an input polynomial after the push. -/
theorem coeff_keep (hL : iL s₀ = 1024) {i : Nat} (hi : i < 256) :
    coeffAt (P0 s₀).mem (iA iP s₀) i = coeffAt s₀.mem (iA iP s₀) i :=
  coeffAt_frame hp.push_frame (fun r hr => by have := hp.in_frame r hr; rwa [inR, hL] at this) hi

/-- The input bytes after the push. -/
theorem bytes_keep {n : Nat} (hn : n ≤ iL s₀) : bytesAt (P0 s₀).mem (iA iP s₀) n = bytesAt s₀.mem (iA iP s₀) n :=
  Proof.MlKem.bytesAt_frame hp.push_frame (fun r hr => (hp.in_frame r hr).sub_left (Region.sub_prefix hn))
    (by have := hp.i_fit; omega)

/-- The leaf's frame and return address are apart from the output. -/
theorem leafW : ∀ r ∈ [outR oP oL s₀], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]; rw [← hp.stk_eq]; exact ⟨hp.stk_o, hp.ret_o⟩

theorem leafE : 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32 := ⟨hp.sp, by have := hp.sp'; omega⟩

/-- The input buffer, after the push. -/
theorem inR_mem : inR iP iL s₀ ∈ (P0 s₀).rd ++ (P0 s₀).wr := by rw [hp.P0_rd]; simp

/-- The output buffer, after the push. -/
theorem outR_mem : outR oP oL s₀ ∈ (P0 s₀).wr := by rw [hp.P0_wr']; simp

end Lay

/-! ## Loading the arguments -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {k i o w : Nat} {iL oL : State → Nat}

theorem ldArgs_ok {s₀ : State} (hp : Lay k (arg · i) (arg · o) iL oL s₀) (hi : i < k) (ho : o < k)
    (hw : w < k) :
    WP isa (.block (ldArgs i o w)) (P0 s₀) fun s =>
      Start (arg · i) (arg · o) s₀ s ∧ s.gpr .eax = arg s₀ w := by
  have fit := hp.sp'
  have hin : argR k s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.wr]; simp
  have a₀ := P0_argAddr s₀ i
  have a₁ := P0_argAddr s₀ o
  have a₂ := P0_argAddr s₀ w
  have i₀ := P0_argIn hi fit hin
  have i₁ := P0_argIn ho fit hin
  have i₂ := P0_argIn hw fit hin
  have v₀ := P0_arg hp.sp hi fit hp.stk_a
  have v₁ := P0_arg hp.sp ho fit hp.stk_a
  have v₂ := P0_arg hp.sp hw fit hp.stk_a
  unfold ldArgs ldPtrs
  xrun [addr, List.cons_append, List.nil_append, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ldPtrs_ok {s₀ : State} (hp : Lay k (arg · i) (arg · o) iL oL s₀) (hi : i < k) (ho : o < k) :
    WP isa (.block (ldPtrs i o)) (P0 s₀) fun s => Start (arg · i) (arg · o) s₀ s := by
  have fit := hp.sp'
  have hin : argR k s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.wr]; simp
  have a₀ := P0_argAddr s₀ i
  have a₁ := P0_argAddr s₀ o
  have i₀ := P0_argIn hi fit hin
  have i₁ := P0_argIn ho fit hin
  have v₀ := P0_arg hp.sp hi fit hp.stk_a
  have v₁ := P0_arg hp.sp ho fit hp.stk_a
  unfold ldPtrs
  xrun [addr, a₀, a₁, i₀, i₁, v₀, v₁]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pointers and the width, from the arguments. -/
theorem ldArgs_piece (hi : i < k) (ho : o < k) (hw : w < k)
    (hL : ∀ s₀, Pre s₀ → Lay k (arg · i) (arg · o) iL oL s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr [.esp]) (.block (ldArgs i o w)) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀)
      (fun s₀ s => (Start (arg · i) (arg · o) s₀ s ∧ s.gpr .eax = arg s₀ w) ∧ True) (.block (ldArgs i o w)) :=
  Piece.taint [.esp] (fun s₀ s h₀ e => by
      subst e; exact (ldArgs_ok (hL s₀ h₀) hi ho hw).mono fun _ h => ⟨h, trivial⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e, e', P0_esp, P0_esp, hpub _ _ h₀ h₀' hq]) ht

/-- The pointers, from the arguments. -/
theorem ldPtrs_piece (hi : i < k) (ho : o < k)
    (hL : ∀ s₀, Pre s₀ → Lay k (arg · i) (arg · o) iL oL s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr [.esp]) (.block (ldPtrs i o)) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) (fun s₀ s => Start (arg · i) (arg · o) s₀ s ∧ True)
      (.block (ldPtrs i o)) :=
  Piece.taint [.esp] (fun s₀ s h₀ e => by
      subst e; exact (ldPtrs_ok (hL s₀ h₀) hi ho).mono fun _ h => ⟨h, trivial⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e, e', P0_esp, P0_esp, hpub _ _ h₀ h₀' hq]) ht

end

/-! ## Branching on the width -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {iP oP : State → BitVec 32}

theorem Start.same {s₀ s s' : State} (h : Start iP oP s₀ s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem)
    (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Start iP oP s₀ s' :=
  ⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm, h.mem], by rw [hg, h.esi],
    by rw [hg, h.edi]⟩

theorem cmp_ok (v : Nat) (s : State) :
    WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.zf = some (s.gpr .eax - BitVec.ofNat 32 v == 0) := by
  xrun

/-- `sel v p e`: `p` if the width `w s₀` (in `eax`) is `v`, and `e` otherwise. -/
theorem sel_piece {X : State → Prop} {B : State → State → Prop} {p e : Prog isa} (w : State → BitVec 32)
    {v : Nat} (hv : v < 2 ^ 32) (hw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → w s₀ = w s₀')
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))]) hc).isSome = true)
    (hp : Piece Pre Pub (fun s₀ s => Start iP oP s₀ s ∧ (X s₀ ∧ (w s₀).toNat = v)) B p)
    (he : Piece Pre Pub (fun s₀ s => (Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ (X s₀ ∧ (w s₀).toNat ≠ v)) B e) :
    Piece Pre Pub (fun s₀ s => (Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ X s₀) B (sel v p e) := by
  refine Piece.seq (B := fun s₀ s => ((Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ X s₀) ∧
      eval .e s = some (decide ((w s₀).toNat = v)))
    (Piece.taint [] (fun s₀ s _ ⟨⟨h, ha⟩, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht)
    (Piece.ite (fun s₀ => decide ((w s₀).toNat = v)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' h₀ h₀' hq => by rw [hw _ _ h₀ h₀' hq])
      (hp.mono (fun _ _ _ ⟨⟨⟨⟨h, _⟩, hx⟩, _⟩, e⟩ => ⟨h, hx, of_decide_eq_true e⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ ⟨⟨⟨h, hx⟩, _⟩, e⟩ => ⟨h, hx, of_decide_eq_false e⟩) fun _ _ _ h => h))
  refine (cmp_ok v s).mono fun s' ⟨hg, hm, hr, hw', hz⟩ => ⟨⟨⟨h.same hg hm hr hw', by rw [hg, ha]⟩, hx⟩, ?_⟩
  simp only [eval, hz, ha, sub_beq_zero, toNat_ofNat32 hv]

end

end VG.Proof.MlDsa.X86.Pack

namespace VG.Proof.MlDsa.X86.Pack

open VG.Spec.MlDsa (coeffAt)

/-! ## Satisfiability -/

/-- A polynomial in memory that is zero below `0x5000` (where the witnesses
of satisfiability put their buffers, with their arguments above) is zero. -/
theorem coeffAt_low {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) {p : Addr}
    (hp : p.toNat + 1024 ≤ 0x5000) {i : Nat} (hi : i < 256) : coeffAt m p i = 0 := by
  rw [coeffAt, Mem.readW_congr (m' := fun _ => 0) fun j hj => hm _ ?_]
  · simp [Mem.readW, Mem.read]
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- The memory of a witness: `ws` at `0x5000 + a` for each `(a, ws)`, zero elsewhere. -/
theorem ite_low {a b : Addr} {x y : Byte} (ha : a.toNat < 0x5000) (hb : 0x5000 ≤ b.toNat) :
    (if a = b then x else y) = y :=
  ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by omega)

end VG.Proof.MlDsa.X86.Pack
