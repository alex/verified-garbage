import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final
import VerifiedGarbage.Proof.Poly1305.X86_64.Setup

/-!
# Poly1305 on x86-64 with AVX2: storing the accumulator

Untrusted: everything here is checked by Lean. `storeH` joins the limbs of
lane 0 of `H` into three words and stores them in the state, the first two
at byte 0 and the last two at byte 8.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq hR contains_off)

def storeV : List Instr := [
  sll (dreg 1) (hreg 1) 26, sll (dreg 2) (hreg 2) 52, v .vpor (dreg 1) (dreg 1) (hreg 0),
  v .vpor (dreg 1) (dreg 1) (dreg 2),
  srl (dreg 2) (hreg 2) 12, sll (dreg 3) (hreg 3) 14, v .vpor (dreg 2) (dreg 2) (dreg 3),
  sll (dreg 3) (hreg 4) 40, v .vpor (dreg 2) (dreg 2) (dreg 3),
  srl (dreg 3) (hreg 4) 24,
  v .vpunpcklqdq tP (dreg 1) (dreg 2)]

theorem storeH_eq : storeH = storeV ++ (([.vmovdquStore .l128 (at_ .rdi 0) tP] : List Instr) ++
    (([v .vpunpcklqdq tP (dreg 2) (dreg 3)] : List Instr) ++
      ([.vmovdquStore .l128 (at_ .rdi 8) tP] : List Instr))) := rfl

def svS : Sym := (Sym.init.run false storeV).get (by decide +kernel)
theorem svS_eq : Sym.init.run false storeV = some svS := (Option.some_get _).symm
def upS : Sym := (Sym.init.run false [v .vpunpcklqdq tP (dreg 2) (dreg 3)]).get (by decide +kernel)
theorem upS_eq : Sym.init.run false [v .vpunpcklqdq tP (dreg 2) (dreg 3)] = some upS :=
  (Option.some_get _).symm

section
variable (E : Env)
theorem svS_d1 : (svS.reg (xi (dreg 1))).natw E 0 = (E.v (xi (hreg 1)) 0 * 2 ^ 26 % 2 ^ 64 |||
    E.v (xi (hreg 0)) 0 ||| E.v (xi (hreg 2)) 0 * 2 ^ 52 % 2 ^ 64) := rfl
theorem svS_d2 : (svS.reg (xi (dreg 2))).natw E 0 = (E.v (xi (hreg 2)) 0 / 2 ^ 12 |||
    E.v (xi (hreg 3)) 0 * 2 ^ 14 % 2 ^ 64 ||| E.v (xi (hreg 4)) 0 * 2 ^ 40 % 2 ^ 64) := rfl
theorem svS_d3 : (svS.reg (xi (dreg 3))).natw E 0 = E.v (xi (hreg 4)) 0 / 2 ^ 24 := rfl
theorem svS_tP : svS.reg (xi tP) = .unpl (svS.reg (xi (dreg 1))) (svS.reg (xi (dreg 2))) := by
  decide +kernel
theorem upS_t0 : (upS.reg (xi tP)).natw E 0 = E.v (xi (dreg 2)) 0 := rfl
theorem upS_t1 : (upS.reg (xi tP)).natw E 1 = E.v (xi (dreg 3)) 0 := rfl
end

theorem st128_ok (s : State) (d : Nat) (hw : InRegions s.wr (off (s.gpr .rdi) d) 16) :
    WP isa (.block [.vmovdquStore .l128 (at_ .rdi d) tP]) s fun s' =>
      s' = s.setMem (s.mem.writeW (off (s.gpr .rdi) d) (s.xmm tP)) := by
  apply WP.of_runBlock
  have e : s.ea (at_ .rdi d) = off (s.gpr .rdi) d := rfl
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128_eq, e, hw, ite_true,
    Option.some.injEq, exists_eq_left']

theorem xmm_lo (s : State) (r : XReg) : (s.xmm r).extractLsb' 0 64 = qw s r 0 := rfl
theorem xmm_hi (s : State) (r : XReg) : (s.xmm r).extractLsb' 64 64 = qw s r 1 := rfl

theorem addr0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- Reading back two overlapping 16-byte stores, at `p` and `p + 8`. -/
theorem two_writes (m : Mem) (p : Addr) (v₁ v₂ : BitVec 128) :
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 0) 64 = v₁.extractLsb' 0 64 ∧
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 8) 64 = v₂.extractLsb' 0 64 ∧
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 16) 64 = v₂.extractLsb' 64 64 := by
  have z : off p 0 = p := by rw [off_eq, addr0]
  have e16 : off p 16 = off p 8 + BitVec.ofNat 64 8 := by rw [off_eq, off_eq, BitVec.add_assoc]; rfl
  have hA := _root_.VG.X86_64.readW_writeW_off (m.writeW p v₁) p v₂ (d := 0) (e := 8) (n := 8) (by omega) (by omega)
    (by omega)
  have hB := readW_writeW_inside m p v₁ (k := 0) (n := 8) (by omega) (by omega)
  have hC := readW_writeW_inside (m.writeW p v₁) (off p 8) v₂ (k := 0) (n := 8) (by omega) (by omega)
  have hD := readW_writeW_inside (m.writeW p v₁) (off p 8) v₂ (k := 8) (n := 8) (by omega) (by omega)
  rw [addr0] at hA hB hC
  rw [← off_eq] at hA
  simp only [Nat.reduceMul] at hA hB hC hD
  rw [z, e16]
  exact ⟨hA.trans hB, hC, hD⟩

/-- The limbs of lane 0 of `H`. -/
def h0 (s : State) : Nat → Nat := hv s 0

/-- What `storeH` leaves: the words of lane 0 of `H` in the state's first 24
bytes, and the rest but the vector registers as it was. -/
structure StorePost (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  frame : Frame [hR (s.gpr .rdi)] s.mem s'.mem
  w0 : (s'.mem.readW (off (s.gpr .rdi) 0) 64).toNat = Limbs26.w0 (h0 s)
  w1 : (s'.mem.readW (off (s.gpr .rdi) 8) 64).toNat = Limbs26.w1 (h0 s)
  w2 : (s'.mem.readW (off (s.gpr .rdi) 16) 64).toNat = h0 s 4 / 2 ^ 24

theorem storeH_ok {s : State} (hw : ∀ d, d + 16 ≤ 24 → InRegions s.wr (off (s.gpr .rdi) d) 16) :
    WP isa (.block storeH) s (StorePost s) := by
  rw [storeH_eq]
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) svS_eq) fun s₁ h₁ => ?_)
  have g₁ := h₁.gpr
  refine WP.block_append (WP.mono (st128_ok s₁ 0 (by rw [h₁.wr, g₁]; exact hw 0 (by omega)))
    fun s₂ e₂ => ?_)
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) upS_eq) fun s₃ h₃ => ?_)
  have hg₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, e₂, State.setMem_gpr, g₁]
  have hw₃ : InRegions s₃.wr (off (s₃.gpr .rdi) 8) 16 := by
    rw [h₃.wr, e₂, State.setMem_wr, h₁.wr, hg₃]; exact hw 8 (by omega)
  refine WP.mono (st128_ok s₃ 8 hw₃) fun s₄ e₄ => ?_
  have hm₃ : s₃.mem = s₁.mem.writeW (off (s.gpr .rdi) 0) (s₁.xmm tP) := by
    rw [h₃.mem, e₂, State.setMem_mem, g₁]
  have m₄ : s₄.mem = (s.mem.writeW (off (s.gpr .rdi) 0) (s₁.xmm tP)).writeW (off (s.gpr .rdi) 8)
      (s₃.xmm tP) := by
    rw [e₄, State.setMem_mem, hm₃, hg₃, h₁.mem]
  -- The words, from the terms.
  have q0 : (qw s₁ tP 0).toNat = Limbs26.w0 (h0 s) := by
    rw [h₁.natw _ (by decide), svS_tP]
    simp only [Q.natw, Nat.reduceMod, ite_true]
    rw [svS_d1]; rfl
  have q1 : (qw s₃ tP 0).toNat = Limbs26.w1 (h0 s) := by
    rw [h₃.natw _ (by decide), upS_t0, envOf_v, e₂]
    change (qw s₁ (dreg 2) 0).toNat = _
    rw [h₁.natw _ (by decide), svS_d2]; rfl
  have q2 : (qw s₃ tP 1).toNat = h0 s 4 / 2 ^ 24 := by
    rw [h₃.natw _ (by decide), upS_t1, envOf_v, e₂]
    change (qw s₁ (dreg 3) 0).toNat = _
    rw [h₁.natw _ (by decide), svS_d3]; rfl
  obtain ⟨r0, r8, r16⟩ := two_writes s.mem (s.gpr .rdi) (s₁.xmm tP) (s₃.xmm tP)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₄, State.setMem_gpr, hg₃]
  · rw [e₄, State.setMem_rd, h₃.rd, e₂, State.setMem_rd, h₁.rd]
  · rw [e₄, State.setMem_wr, h₃.wr, e₂, State.setMem_wr, h₁.wr]
  · have vm : ∀ {a b : State}, vec a b = b → b.mxcsr = a.mxcsr := fun h => by rw [← h]; rfl
    rw [e₄, show ∀ t m, (State.setMem t m).mxcsr = t.mxcsr from fun _ _ => rfl, vm h₃.eq, e₂,
      show ∀ t m, (State.setMem t m).mxcsr = t.mxcsr from fun _ _ => rfl, vm h₁.eq]
  · rw [m₄]
    exact ((Frame.refl [hR (s.gpr .rdi)] s.mem).writeW (List.mem_singleton_self _) _
      (contains_off (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (contains_off (by omega) (by omega))
  · rw [m₄, r0, xmm_lo, q0]
  · rw [m₄, r8, xmm_lo, q1]
  · rw [m₄, r16, xmm_hi, q2]

end VG.Proof.Poly1305.X86_64.Avx2
