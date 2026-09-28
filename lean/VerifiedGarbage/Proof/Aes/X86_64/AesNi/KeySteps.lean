import VerifiedGarbage.Proof.Aes.X86_64.AesNi.KeyWords
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# AES-NI key expansion: the steps

Untrusted: everything here is checked by Lean. What `kstep` and `kstepB6`
compute, as doublewords (one symbolic execution of each, for any registers
and offsets), and `good_store`: storing a register whose first `n`
doublewords are the next `n` words of the schedule extends the stored
prefix of the schedule by `n` words.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ kstep kstepB6)

/-! ## Doublewords -/

/-- `pslldq x, 4`. -/
def sh (x : BitVec 128) : BitVec 128 := x <<< 32

theorem pslldq4 (x : BitVec 128) : XShiftOp.eval .pslldq x 4 = sh x := rfl

theorem eval_pxor' (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem dword_xor (a b : BitVec 128) (j : Nat) : dword (a ^^^ b) j = dword a j ^^^ dword b j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

theorem dword_sh0 (x : BitVec 128) : dword (sh x) 0 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  simp; omega

theorem dword_sh (x : BitVec 128) {j : Nat} (hj : j < 3) : dword (sh x) (j + 1) = dword x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [decide_eq_true (by omega), decide_eq_false (by omega), Bool.not_false, Bool.true_and,
    Bool.true_and]
  exact congrArg _ (by omega)

theorem dword_sh1 (x : BitVec 128) : dword (sh x) 1 = dword x 0 := dword_sh x (j := 0) (by decide)
theorem dword_sh2 (x : BitVec 128) : dword (sh x) 2 = dword x 1 := dword_sh x (j := 1) (by decide)
theorem dword_sh3 (x : BitVec 128) : dword (sh x) 3 = dword x 2 := dword_sh x (j := 2) (by decide)

/-- `prefixXor(x) ⊕ t`, as `kstep` computes it. -/
def kv (x t : BitVec 128) : BitVec 128 := x ^^^ sh x ^^^ sh (sh x) ^^^ sh (sh (sh x)) ^^^ t

theorem dword_kv (x t : BitVec 128) :
    dword (kv x t) 0 = dword x 0 ^^^ dword t 0 ∧
    dword (kv x t) 1 = dword x 1 ^^^ (dword x 0 ^^^ dword t 1) ∧
    dword (kv x t) 2 = dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 2)) ∧
    dword (kv x t) 3 = dword x 3 ^^^ (dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 3))) := by
  simp only [kv, dword_xor, dword_sh0, dword_sh1, dword_sh2, dword_sh3, BitVec.zero_xor,
    BitVec.xor_assoc, and_self]

/-- `[b₀, b₀ ⊕ b₁, …] ⊕ t`, as `kstepB6` computes it. -/
def kb (b t : BitVec 128) : BitVec 128 := b ^^^ sh b ^^^ t

theorem dword_kb (b t : BitVec 128) :
    dword (kb b t) 0 = dword b 0 ^^^ dword t 0 ∧
    dword (kb b t) 1 = dword b 1 ^^^ (dword b 0 ^^^ dword t 1) := by
  simp only [kb, dword_xor, dword_sh0, dword_sh1, BitVec.zero_xor, BitVec.xor_assoc, and_self]

theorem shuf_ff (x : BitVec 128) :
    shufDwords x 0xff = ofDwords (dword x 3) (dword x 3) (dword x 3) (dword x 3) := rfl
theorem shuf_55 (x : BitVec 128) :
    shufDwords x 0x55 = ofDwords (dword x 1) (dword x 1) (dword x 1) (dword x 1) := rfl
theorem shuf_aa (x : BitVec 128) :
    shufDwords x 0xaa = ofDwords (dword x 2) (dword x 2) (dword x 2) (dword x 2) := rfl

theorem kga1 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 1 = (sub32 (dword x 1)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_1]; rfl

theorem kga2 (x : BitVec 128) (r : BitVec 8) : dword (aesKeygenAssist x r) 2 = sub32 (dword x 3) := by
  simp only [aesKeygenAssist, dword_ofDwords_2]; rfl

theorem kga3 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 3 = (sub32 (dword x 3)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_3]; rfl

/-! ## The steps -/

theorem kstep_exec (d s : XReg) (sel r : BitVec 8) (off : Nat) (st : State) (hd3 : d ≠ .xmm3)
    (hd4 : d ≠ .xmm4) (hw : InRegions st.wr (st.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16) :
    WP isa (.block (kstep d s sel r off)) st fun st' =>
      st'.xmm d = kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel) ∧
      st'.mem = st.mem.writeW (st.gpr .rdx + BitVec.ofInt 64 (off : Int))
        (kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [kstep, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hw, ite_true, ite_false, hd3, hd4, Ne.symm hd3, Ne.symm hd4,
    Option.some.injEq, exists_eq_left', eval_movdqa, pslldq4, eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

theorem kstepB6_exec (off : Nat) (st : State)
    (hw : InRegions st.wr (st.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16) :
    WP isa (.block (kstepB6 off)) st fun st' =>
      st'.xmm .xmm2 = kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff) ∧
      st'.mem = st.mem.writeW (st.gpr .rdx + BitVec.ofInt 64 (off : Int))
        (kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [kstepB6, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hw, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', eval_movdqa, pslldq4, eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

/-! ## The stored words -/

/-- Words `0 … K − 1` of `f` are stored at `p`, as little-endian doublewords. -/
def Good (m : Mem) (p : Addr) (f : Nat → BitVec 32) (K : Nat) : Prop :=
  ∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i

theorem good_store {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K : Nat} (hG : Good m p f K)
    (v : BitVec 128) {n : Nat} (hn : n ≤ 4) (hv : ∀ j < n, dword v j = f (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    Good (m.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + n) := by
  intro i hi
  by_cases h : i < K
  · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
    exact hG i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = K + j := ⟨i - K, by omega⟩
    rw [show 4 * (K + j) = 4 * K + 4 * j by omega, ofNat_add', readW_writeW128 _ _ _ (by omega)]
    exact hv j (by omega)

theorem Good.mono {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K K' : Nat} (h : Good m p f K)
    (hK : K' ≤ K) : Good m p f K' := fun i hi => h i (by omega)

end VG.Proof.Aes.X86_64.AesNi
