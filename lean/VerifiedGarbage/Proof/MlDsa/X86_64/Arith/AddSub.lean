import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ML-DSA on x86-64: `vg_mldsa_add` and `vg_mldsa_sub`

Untrusted: everything here is checked by Lean. Each iteration of the loop
stores four coefficients to `f` (`addBody_ok`, `subBody_ok`), each `csubL`
of the sum (`caddL` of the difference), whose value is `addD_toNat`
(`subD_toNat`); the loop leaves `f` with all 256 (`AddSub.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of ifp ifn ptr_step GOnly wp_rcxLoop xmm_setXmm
  add_ofNat_zero)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## Four coefficients -/

/-- What an iteration of `add` stores. -/
def addV (x y : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddd x y)

/-- What an iteration of `sub` stores. -/
def subV (x y : BitVec 128) : BitVec 128 := caddV (XBinOp.eval .psubd x y)

theorem dword_addV (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (addV x y) i = csubL (dword x i + dword y i) := by
  rw [addV, dword_csubV _ hi, dword_paddd _ _ hi]

theorem dword_subV (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (subV x y) i = caddL (dword x i - dword y i) := by
  rw [subV, dword_caddV _ hi, dword_psubd _ _ hi]

/-- The body of `add` or `sub`: the store of `F x y` of the vectors at `rdi`
and `rsi`, and the counts. -/
theorem accBody_ok {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    (hF : ∀ (s : State), s.xmm .xmm15 = qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = qV)
    (s : State) (hq : s.xmm .xmm15 = qV) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) (h3 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++
        ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))))) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi) (F (s.mem.readW (s.gpr .rdi) 128) (s.mem.readW (s.gpr .rsi) 128)) ∧
        s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm .xmm15 = qV ∧
        Keep [.rdi, .rsi, .rcx] s s' := by
  rw [WP.block_append_iff]
  vrund [h1, h2]
  rw [show Instr.xop (.bin op .xmm0 .xmm1) :: (fix ++ (accTail ++ [.alu .sub .rcx (.imm 1)])) =
    (xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (hF _ (by simp only [xmm_setXmm, reduceCtorEq, ite_false]; exact hq))
    fun s2 ⟨h0, g2, m2, r2, w2, q2⟩ => ?_
  simp only [accTail]
  vrund [g2, m2, r2, w2, h3, h0, q2]
  refine ⟨fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

theorem addFix_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = addV (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.xmm .xmm15 = qV := by
  simp only [vcsub, vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

theorem subFix_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = subV (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.xmm .xmm15 = qV := by
  simp only [vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

/-! ## The loop -/

namespace AddSub

/-- After `i` vectors, each coefficient before `4i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : s.xmm .xmm15 = qV
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 4 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
include hp

/-- An iteration, which stores `F` of the vectors of `f` and `g`, whose
doublewords are `L` of theirs. -/
theorem step {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    {L : BitVec 32 → BitVec 32 → BitVec 32}
    (hF : ∀ (s : State), s.xmm .xmm15 = qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = qV)
    (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
    {i : Nat} (hi : i < 64) {s : State}
    (hI : Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++
        ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))))) s fun s' =>
      Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i) := by rw [hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (4 * i) := by rw [hI.rsi]; congr 2; omega
  refine WP.mono (accBody_ok hF s hI.q (by rw [e1]; exact f_in (List.mem_append_right _ hw) j0)
    (by rw [e2]; exact ⟨_, hr, pR_contains _ j0⟩) (by rw [e1]; exact f_in hw j0))
    fun s' ⟨hm, hdi, hsi, hcx, hz, hrd, hwr, hq, _⟩ => ⟨?_, hcx, hz⟩
  refine ⟨by rw [hdi, hI.rdi]; exact ptr_step _ i 16, by rw [hsi, hI.rsi]; exact ptr_step _ i 16,
    hrd.trans hI.rd, hwr.trans hI.wr, hq, ?_, fun k hk => ?_⟩
  · rw [hm, e1]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains _ j0)
  · rw [hm, e1, coeffAt_write128 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 4 * (i + 1) by omega), hL _ _ _ (by omega), e2, dword_readW _ _ (by omega),
        dword_readW _ _ (by omega), coeffAddr_add, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq,
        show 4 * i + (k - 4 * i) = k by omega, hI.coeff k hk, ifn (by omega),
        coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) (by rw [n_eq]; exact hk)]
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 4 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]

/-- The whole function, from its precondition. -/
theorem fn_ok {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
    {L : BitVec 32 → BitVec 32 → BitVec 32}
    (hF : ∀ (s : State), s.xmm .xmm15 = qV →
      WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
        s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
          s'.wr = s.wr ∧ s'.xmm .xmm15 = qV)
    (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
    (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail))) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail)) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
        (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
          accTail))) s₀ tr s' ∧ abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hw : pR (s₀.gpr .rdi) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa (.seq (.block qPro) (VG.Impl.MlKem.X86_64.rcxLoop 64
      (([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] : List Instr) ++ (xb op .xmm0 .xmm1 :: fix) ++
        accTail))) s₀
      (Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) 64) := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm15 = qV ∧ Keep [.rax] s₀ w ∧ w.mem = s₀.mem)
      (by
        simp only [qPro]
        vrund
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun w ⟨hq, k1, m1⟩ => ?_)
    refine wp_rcxLoop (N := 64) (by decide) (by decide) _ (fun u o _ => ⟨?_, ?_, by rw [o.keep.2.1, k1.2.1],
      by rw [o.keep.2.2, k1.2.2], by rw [o.xmm]; exact hq, by rw [o.mem, m1]; exact Frame.refl _ _,
      fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩) fun i hi u hI => ?_
    · rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero]
    · rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero]
    · rw [show [Instr.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] ++
          (xb op .xmm0 .xmm1 :: fix) ++ accTail ++ [.alu .sub .rcx (.imm 1)] =
          [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0)] ++
          ((xb op .xmm0 .xmm1 :: fix) ++ (accTail ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) by
        simp only [List.append_assoc]]
      exact step hp hF hL hi hI
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hI.coeff k hk, ifp (by omega)]
    exact hv k hk

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.add s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.add).post s s' :=
  AddSub.fn_ok hs (op := .paddd) (fix := vcsub .xmm0 .xmm2) (L := fun a b => csubL (a + b)) addFix_ok
    (fun x y e he => dword_addV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [add_get _ _ hk', addD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_add])
    (by decide +kernel) (by decide +kernel)

theorem sub_correct (s : State) (hs : (accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.sub s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.sub).post s s' :=
  AddSub.fn_ok hs (op := .psubd) (fix := vcadd .xmm0 .xmm2) (L := fun a b => caddL (a - b)) subFix_ok
    (fun x y e he => dword_subV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [sub_get _ _ hk', subD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_sub])
    (by decide +kernel) (by decide +kernel)

/-- The pointers and `rsp` are public. -/
def accτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : X86_64.Taint.Agree accτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem add_ct :
    ConstantTime isa (accK Spec.MlDsa.add).pre (accK Spec.MlDsa.add).pub Impl.MlDsa.X86_64.Arith.add :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem sub_ct :
    ConstantTime isa (accK Spec.MlDsa.sub).pre (accK Spec.MlDsa.sub).pub Impl.MlDsa.X86_64.Arith.sub :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.add (Spec.MlDsa.addContract X86_64.abi) :=
  Verified.of_correct add_correct add_ct (by
    mldsa_implies [Spec.MlDsa.addContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem sub_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.sub (Spec.MlDsa.subContract X86_64.abi) :=
  Verified.of_correct sub_correct sub_ct (by
    mldsa_implies [Spec.MlDsa.subContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlDsa.X86_64.Arith
