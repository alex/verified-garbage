import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Call
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# ML-DSA verification on x86-64: entry to a callee

Untrusted: everything here is checked by Lean. What a callee's contract
needs on its entry, from the layout of the caller: that its buffers are
apart from its return address and the 16 bytes of stack below it, and from
each other, and that they read on entry as they did before the call
(`Ent`). And what the callees must be (`CalleeOk`): correct and constant
time under their contracts with 16 bytes of stack (24 for
`vg_mldsa_rej_ntt_poly4`), not writing the stack pointer, calling at most
three deep, and never loading MXCSR.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Callees -/

/-- A callee: correct and constant time under the contract `k` (a shared
contract), not writing `rsp`, calling at most three deep, loading MXCSR only
to restore it (`ctlOk`), and never writing the stack pointer (which its
callers' artifacts check). -/
structure CalleeOk (c : Prog isa) (k : Contract isa) : Prop where
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  spSafe : c.all (fun i => !isa.writesSp i) = true

/-- A callee verified against its shared contract with at most 16 bytes of stack. -/
theorem CalleeOk.of_verified {c : Prog isa} {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words X86_64.abi.ptrBits) (Mem → List Nat))} {n : Nat}
    (h : Verified X86_64.target c (sig.contract X86_64.abi pre post wa n leak)) (hn : n ≤ 16)
    (hsp : NoSp c) (hd : c.depth ≤ 3) (hmx : ctlOk c = true)
    (hss : c.all (fun i => !isa.writesSp i) = true) :
    CalleeOk c (sig.contract X86_64.abi pre post wa 16 leak) :=
  ⟨fun s hs => h.1 s (pre_stack hn hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => h.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (pre_stack hn h₁) (pre_stack hn h₂) hp e₁ e₂,
    hsp, hd, hmx, hss⟩

/-! ## Entry

A callee's precondition, evaluated, is stated on the state of the call
instruction: its stack pointer is 8 below the caller's, and its memory the
caller's with the return address written below it. -/

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
include L

theorem Lay.sp16 : 16 ≤ (s.gpr .rsp - 8).toNat := by
  have := L.sp32
  rw [BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem Lay.ret8 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8)) + 24 by bv_omega, BitVec.toNat_add]
  have : (24 : BitVec 64).toNat = 24 := rfl
  omega

theorem Lay.stk16 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8 - 16, 16⟩ ⟨pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8 - 16)) + 8 by bv_omega, BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := rfl
  omega

theorem Lay.sp24 : 24 ≤ (s.gpr .rsp - 8).toNat := by
  have := L.sp32
  rw [BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem Lay.stk24 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8 - 24, 24⟩ ⟨pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = x - (s.gpr .rsp - 8 - 24) by bv_omega]
  omega

theorem Lay.wbytes {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (v : BitVec 64) :
    ∀ i < l, (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p + BitVec.ofNat 64 i) = s.mem (pa s p + BitVec.ofNat 64 i) :=
  fun i hi => Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (R := ⟨pa s p, l⟩) (by
      simp only [List.mem_singleton, forall_eq]
      exact ((L.stkD h).sub_left (below_sub (by omega) (by omega))).symm)
    (by have := L.nwp h; simp; omega) hi

theorem Lay.wbytesAt {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (v : BitVec 64) :
    bytesAt (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) l = bytesAt s.mem (pa s p) l :=
  Proof.MlKem.bytesAt_congr (L.wbytes h v)

theorem Lay.wpolyAt {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    polyAt (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) = polyAt s.mem (pa s p) :=
  Proof.MlDsa.Verify.polyAt_congr (L.wbytes h v)

theorem Lay.wnatPolyAt {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    natPolyAt (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) = natPolyAt s.mem (pa s p) :=
  Proof.MlDsa.Verify.natPolyAt_congr (L.wbytes h v)

theorem Lay.wcoeffAt {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) {i : Nat} (hi : i < n) :
    coeffAt (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) i = coeffAt s.mem (pa s p) i :=
  Proof.MlDsa.Verify.coeffAt_congr (L.wbytes h v) hi

theorem Lay.whintAt {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    hintAt (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) 1 = hintAt s.mem (pa s p) 1 := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have : i = 0 := by rw [List.mem_range] at hi; omega
  subst this
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  rw [L.wcoeffAt h v hj]

theorem Lay.wreduced {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) (hr : Reduced s.mem (pa s p)) :
    Reduced (s.mem.writeW (s.gpr .rsp - 8) v) (pa s p) :=
  Proof.MlDsa.Verify.reduced_congr (L.wbytes h v) hr

end

/-- The values of the arguments after their moves. -/
theorem Args.reg {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) {r : Reg} {a : Arg} (ha : (r, a) ∈ as) :
    s1.gpr r = a.val s := h.1.1 _ ha

theorem Args.r0 {r : Reg} {a : Arg} {as : List (Reg × Arg)} {s s1 : State} (h : Args ((r, a) :: as) s s1) :
    s1.gpr r = a.val s := h.1.1 _ (List.mem_cons_self ..)

theorem Args.r1 {r r1 : Reg} {a a1 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem Args.r2 {r r1 r2 : Reg} {a a1 a2 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem Args.r3 {r r1 r2 r3 : Reg} {a a1 a2 a3 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem Args.r4 {r r1 r2 r3 r4 : Reg} {a a1 a2 a3 a4 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))

theorem Args.r5 {r r1 r2 r3 r4 r5 : Reg} {a a1 a2 a3 a4 a5 : Arg} {as : List (Reg × Arg)} {s s1 : State}
    (h : Args ((r5, a5) :: (r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

theorem Args.rsp {as : List (Reg × Arg)} {s s1 : State} (h : Args as s s1) : s1.gpr .rsp = s.gpr .rsp :=
  h.2.gpr (by decide)

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem imm64 {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  simp only [BitVec.toNat_ofNat]; omega

/-- Two states whose layout registers and stack pointer agree. -/
def SameB (x y : State) : Prop := (∀ r ∈ bases, x.gpr r = y.gpr r) ∧ x.gpr .rsp = y.gpr .rsp

theorem SameB.pa {x y : State} (h : SameB x y) {p : Ptr} (hp : p.1 ∈ bases) : pa x p = pa y p := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa, h.1 _ hp]

/-- The buffers of a layout: small, in the registers `bases`. -/
def LayOk (bs : List (Reg × Nat)) : Prop := ∀ b ∈ bs, b.2 < 2 ^ 31 ∧ b.1 ∈ bases

theorem Lay.ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) : LayOk (rbs ++ wbs) :=
  fun b hb => ⟨L.small b hb, L.bs b hb⟩

theorem ptr_ok {bs : List (Reg × Nat)} (L : LayOk bs) {p : Ptr} {l : Nat}
    (h : inB bs p l = true) : (Arg.ptr p).Ok := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  refine ⟨by have := (L _ hn).1; simp only at this; omega, fun h' => ?_⟩
  have := (L _ hn).2
  simp only at this
  revert h' this
  generalize p.1 = r
  cases r <;> decide

theorem ptr_bs {bs : List (Reg × Nat)} (L : LayOk bs) {p : Ptr} {l : Nat}
    (h : inB bs p l = true) : p.1 ∈ bases := by
  obtain ⟨n, hn, _⟩ := inB_spec h
  exact (L _ hn).2

end VG.Proof.MlDsa.X86_64.Verify
