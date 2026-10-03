import VerifiedGarbage.Proof.Md5.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Md5.X86_64.Avx512
import VerifiedGarbage.Proof.Md5.X86_64.Avx512.Lit

/-!
# MD5 compression function on x86-64 with AVX-512

The proof follows the scalar one (`Proof/Md5/X86_64/Compress.lean`), whose
contract, precondition and invariant between blocks it shares, with the words
in doubleword 0 of `xmm` registers. Each operation is the addition of
`X[k] + T[t+1]` (`head_ok`), the auxiliary function of its round, symbolically
executed once per round (`fn_ok`), and the rotation and the addition of `b`
(`tail_ok`).
-/

namespace VG.Proof.Md5.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Md5.X86_64.Avx512
open VG.Impl.Md5.X86_64 (at_ rot advance)
open VG.Proof.Md5.X86_64 (Pre Common st bp nb blkAddr blk stR H₀ ea_at ofInt_natCast stateAt_eq
  stateAt_get blk_word compressBlocks_succ test_ok contains_offset')
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I stateAt compressBlocks)

/-- The words `v` are in doubleword 0 of the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  dword (s.xmm (var t 0)) 0 = v[0] ∧ dword (s.xmm (var t 1)) 0 = v[1] ∧
  dword (s.xmm (var t 2)) 0 = v[2] ∧ dword (s.xmm (var t 3)) 0 = v[3]

/-- The registers that hold pointers and the count, and `rsp`: never written by the operations. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega

theorem var_aux : ∀ c < 4, ∀ i < 4,
    work.getD ((i + 4 - c) % 4) .xmm0 ≠ T0 ∧ work.getD ((i + 4 - c) % 4) .xmm0 ≠ XK := by decide

theorem var_ne_T0 (t k : Nat) (hk : k < 4) : var t k ≠ T0 := (var_aux (t % 4) (Nat.mod_lt _ (by omega)) k hk).1

theorem var_ne_XK (t k : Nat) (hk : k < 4) : var t k ≠ XK := (var_aux (t % 4) (Nat.mod_lt _ (by omega)) k hk).2

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .xmm0 ≠ work.getD ((j + 4 - c) % 4) .xmm0 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem dword_tern (r : Nat) (hr : r < 4) (a b c : BitVec 128) :
    dword (ternlog a b c (tern r)) 0 = roundFn r (dword b 0) (dword c 0) (dword a 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [tern, ternlog, List.range, List.range.loop, List.foldl, ite_true,
    ite_false, Nat.testBit] <;>
  simp only [roundFn, F, G, H, I, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_xor, hk, decide_true, Bool.true_and, Nat.zero_add, Nat.mul_zero,
    show k < 128 by omega] <;>
  cases a.getLsbD k <;> cases b.getLsbD k <;> cases c.getLsbD k <;> simp

theorem dword_rolDwords (x : BitVec 128) (n : BitVec 8) :
    dword (rolDwords x n) 0 = (dword x 0).rotateLeft (n.toNat % 32) := by
  simp only [rolDwords, dword_ofDwords_0]

theorem dword_vmovq (x : BitVec 64) : dword ((0 : BitVec 64) ++ x) 0 = x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hk,
    show k < 64 by omega, decide_true, Bool.true_and, ite_true, Nat.zero_add, Nat.mul_zero]

theorem lane0 (s : State) (r : XReg) : s.lane r 0 = s.xmm r := rfl

/-! ## One operation -/

/-- The instructions of an operation before the auxiliary function. -/
def headI (a : XReg) (k : Nat) (T : Word) : List Instr :=
  [.mov32 R (.mem (at_ .rsi (4 * k))), .alu32 .add R (.imm T), .vop (.vmovq XK R),
    .vop (.vbin .vpaddd .l128 a a XK)]

/-- The auxiliary function of round `r`, added into `a`. -/
def fnI (r : Nat) (a b c d : XReg) : List Instr :=
  [.vop (.vmovdqa .l128 T0 d), .vop (.vpternlogd .l128 T0 b c (tern r)),
    .vop (.vbin .vpaddd .l128 a a T0)]

/-- The rotation and the addition of `b`. -/
def tailI (a b : XReg) (n : Nat) : List Instr :=
  [.vop (.vprold .l128 a a (BitVec.ofNat 8 n)), .vop (.vbin .vpaddd .l128 a a b)]

theorem step_split (t : Nat) :
    step t = headI (var t 0) (ks.getD t 0) (Ts.getD t 0) ++
      (fnI (t / 16) (var t 0) (var t 1) (var t 2) (var t 3) ++ tailI (var t 0) (var t 1) (rot t)) := rfl

theorem head_ok (a : XReg) (k : Nat) (T : Word) (ha : a ≠ XK)
    (s : State) (va x : Word) (bp : Addr) (h₁ : dword (s.xmm a) 0 = va)
    (hrsi : s.gpr .rsi = bp) (hin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hx : s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = x) :
    WP isa (.block (headI a k T)) s fun s' =>
      dword (s'.xmm a) 0 = va + (x + T) ∧ (∀ r, r ≠ a → r ≠ XK → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ R → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [headI, R, XK, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32, State.ea, State.load32, at_, VOp.exec, lane0,
    isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, ite_true,
    hrsi, hin, hx, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [XK] at ha
  refine ⟨?_, fun r hr hr' => by simp [hr, hr'], fun r hr => by simp [hr], trivial⟩
  simp only [ha, ite_false, VBinOp.sse, dword_paddd _ _ (show 0 < 4 by decide), h₁, dword_vmovq,
    RegUpd.setWidth_setWidth_32]

theorem fn_ok (r : Nat) (hr : r < 4) (a b c d : XReg) (ha : a ≠ T0) (hb : b ≠ T0) (hc : c ≠ T0)
    (s : State) (va vb vc vd : Word) (h₀ : dword (s.xmm a) 0 = va) (h₁ : dword (s.xmm b) 0 = vb)
    (h₂ : dword (s.xmm c) 0 = vc) (h₃ : dword (s.xmm d) 0 = vd) :
    WP isa (.block (fnI r a b c d)) s fun s' =>
      dword (s'.xmm a) 0 = va + roundFn r vb vc vd ∧ (∀ x, x ≠ a → x ≠ T0 → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [fnI, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, lane0, isa,
    RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, ite_true,
    ha, hb, hc, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun x hx hx' => by simp [hx, hx'], trivial, trivial, trivial, trivial⟩
  simp only [VBinOp.sse]
  rw [dword_paddd _ _ (by decide), dword_tern r hr, h₀, h₁, h₂, h₃]

theorem tail_ok (a b : XReg) (n : Nat) (hn : n < 32) (hab : a ≠ b)
    (s : State) (va vb : Word) (h₁ : dword (s.xmm a) 0 = va) (h₂ : dword (s.xmm b) 0 = vb) :
    WP isa (.block (tailI a b n)) s fun s' =>
      dword (s'.xmm a) 0 = va.rotateLeft n + vb ∧ (∀ x, x ≠ a → s'.xmm x = s.xmm x) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  apply WP.of_runBlock
  simp only [tailI, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, lane0, isa,
    RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, ite_true,
    hba, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun x hx => by simp [hx], trivial, trivial, trivial, trivial⟩
  simp only [VBinOp.sse]
  rw [dword_paddd _ _ (by decide), dword_rolDwords, h₁, h₂, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 8 by omega), Nat.mod_eq_of_lt hn]

/-- The additions in the order of the code. -/
theorem add_fn (a x T f : Word) : a + (x + T) + f = a + f + x + T := by ac_rfl

theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : Addr)
    (hv : Vars t s v) (hrsi : s.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  have n01 := var_ne t (i := 0) (j := 1) (by omega) (by omega) (by omega)
  have n02 := var_ne t (i := 0) (j := 2) (by omega) (by omega) (by omega)
  have n03 := var_ne t (i := 0) (j := 3) (by omega) (by omega) (by omega)
  rw [step_split, WP.block_append_iff]
  refine WP.mono (head_ok (var t 0) (ks.getD t 0) (Ts.getD t 0) (var_ne_XK t 0 (by omega)) s v[0]
    (X ⟨ks.getD t 0, hk⟩) bp h0 hrsi (hin _ hk) (hX _ hk))
    fun s₁ ⟨a₁, e₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  have b₁ : s₁.xmm (var t 1) = s.xmm (var t 1) := e₁ _ n01.symm (var_ne_XK t 1 (by omega))
  refine WP.mono (fn_ok (t / 16) (by omega) _ _ _ _ (var_ne_T0 t 0 (by omega)) (var_ne_T0 t 1 (by omega))
    (var_ne_T0 t 2 (by omega)) s₁ _ v[1] v[2] v[3] a₁ (by rw [b₁]; exact h1)
    (by rw [e₁ _ n02.symm (var_ne_XK t 2 (by omega))]; exact h2)
    (by rw [e₁ _ n03.symm (var_ne_XK t 3 (by omega))]; exact h3))
    fun s₂ ⟨a₂, e₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (tail_ok (var t 0) (var t 1) (rot t) (by omega) n01 s₂ _ v[1] a₂
    (by rw [e₂ _ n01.symm (var_ne_T0 t 1 (by omega)), b₁]; exact h1))
    fun s₃ ⟨a₃, e₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have x : ∀ k, 0 < k → k < 4 → s₃.xmm (var t k) = s.xmm (var t k) := fun k hk h4 => by
    have hne := (var_ne t (i := 0) (j := k) (by omega) h4 (by omega)).symm
    rw [e₃ _ hne, e₂ _ hne (var_ne_T0 t k h4), e₁ _ hne (var_ne_XK t k h4)]
  refine ⟨?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr => ?_⟩
  · rw [step_eq X v ht]
    simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
      var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), stepKX,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [x 3 (by omega) (by omega), h3]
    · rw [a₃, BitVec.add_comm (v[1]), add_fn]
    · rw [x 1 (by omega) (by omega), h1]
    · rw [x 2 (by omega) (by omega), h2]
  · rw [g₃, g₂, g₁ r (fun h => by subst h; simp [pubRegs, R] at hr)]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : Addr) (sB : State) (hrsi : sB.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_rsi (by rw [hs.rd, hs.wr]; exact hin)
      (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

/-! ## Between blocks -/

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    dword (s.xmm .xmm0) 0 = v[0] ∧ dword (s.xmm .xmm1) 0 = v[1] ∧
    dword (s.xmm .xmm2) 0 = v[2] ∧ dword (s.xmm .xmm3) 0 = v[3] := Iff.rfl

theorem dword_shuf (w : BitVec 128) :
    dword (shufDwords w 0x55) 0 = dword w 1 ∧ dword (shufDwords w 0xaa) 0 = dword w 2 ∧
      dword (shufDwords w 0xff) 0 = dword w 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [dword_shufDwords _ _ (by decide)] <;> rfl

/-- `spread` gives each word its register. -/
theorem spread_ok (s : State) :
    WP isa (.block spread) s fun s' =>
      dword (s'.xmm .xmm0) 0 = dword (s.xmm .xmm0) 0 ∧ dword (s'.xmm .xmm1) 0 = dword (s.xmm .xmm0) 1 ∧
      dword (s'.xmm .xmm2) 0 = dword (s.xmm .xmm0) 2 ∧ dword (s'.xmm .xmm3) 0 = dword (s.xmm .xmm0) 3 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3⟩ := dword_shuf (s.xmm .xmm0)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [spread, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, lane0, isa, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, ite_true, ite_false, Option.some.injEq, exists_eq_left', h1, h2, h3]

theorem ea_rdi (s : State) : s.ea (at_ .rdi 0) = s.gpr .rdi := by
  simp [ea_at]

theorem load_split : load = ([.vmovdquLoad .l128 .xmm0 (at_ .rdi 0)] : List Instr) ++ spread := rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ s₁.gpr = s.gpr ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : InRegions (s.rd ++ s.wr) (st s₀) 16 := by
    rw [hrd, hwr]
    exact ⟨stR s₀, by simp [hp.wr], Region.contains_self _ _⟩
  rw [load_split, WP.block_append_iff]
  refine WP.mono (Q := fun (s₁ : State) => s₁.xmm .xmm0 = s.mem.readW (st s₀) 128 ∧ s₁.gpr = s.gpr ∧
    s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem) ?_ fun s₁ ⟨x₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, ea_rdi, hrdi, State.load128, hin,
      ite_true, Option.map_some, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
      RegUpd.wr_setV, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  refine WP.mono (spread_ok s₁) fun s₂ ⟨d0, d1, d2, d3, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine ⟨?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [m₂, m₁]⟩
  simp only [vars0, d0, d1, d2, d3, x₁, dword_readW _ _ (show 0 < 4 by decide),
    dword_readW _ _ (show 1 < 4 by decide), dword_readW _ _ (show 2 < 4 by decide),
    dword_readW _ _ (show 3 < 4 by decide), stateAt_get _ _ (show 0 < 4 by decide),
    stateAt_get _ _ (show 1 < 4 by decide), stateAt_get _ _ (show 2 < 4 by decide),
    stateAt_get _ _ (show 3 < 4 by decide), ofInt_natCast]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The instructions of `update` before `spread`. -/
def addI : List Instr :=
  [.vop (.vbin .vpunpckldq .l128 .xmm4 .xmm0 .xmm1), .vop (.vbin .vpunpckldq .l128 .xmm5 .xmm2 .xmm3),
    .vop (.vbin .vpunpcklqdq .l128 .xmm4 .xmm4 .xmm5), .vmovdquLoad .l128 .xmm5 (at_ .rdi 0),
    .vop (.vbin .vpaddd .l128 .xmm0 .xmm4 .xmm5), .vmovdquStore .l128 (at_ .rdi 0) .xmm0]

theorem update_split : update ++ advance = addI ++ (spread ++ advance) := rfl

theorem add_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) →
      s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block addI) s fun s' =>
      s'.mem = s.mem.writeW (st s₀) (s'.xmm .xmm0) ∧
      (∀ k (hk : k < 4), dword (s'.xmm .xmm0) k = V[k] + H[k]) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (st s₀) 16 := by
    rw [hrd, hwr]
    exact ⟨stR s₀, by simp [hp.wr], Region.contains_self _ _⟩
  have hout : InRegions s.wr (st s₀) 16 := by
    rw [hwr]
    exact ⟨stR s₀, by simp [hp.wr], Region.contains_self _ _⟩
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addI, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    lane0, isa, ea_rdi, State.load128, State.store128_eq, hin, hout, hrdi, ite_true, ite_false,
    Option.map_some, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, State.setMem_xmm, State.setMem_gpr, State.setMem_mem, State.setMem_rd, State.setMem_wr,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ?_, trivial⟩
  simp only [VBinOp.sse, dword_paddd _ _ hk, punpcklqdq_eq, dword_punpckldq, dword_readW _ _ hk, hH k hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, v0, v1, v2, v3]

theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr .rdi = s.gpr .rdi ∧ s'.xmm = s.xmm ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.zf_setReg, RegUpd.xmm_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.xmm_arithFlags, ite_true,
    ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  exact ⟨by rw [e64], by rw [e1], by rw [e1], trivial⟩

theorem stateAt_writeW128 (m : Mem) (p : Addr) (w : BitVec 128) (v : HashValue)
    (h : ∀ k (hk : k < 4), dword w k = v[k]) : stateAt (m.writeW p w) p = v :=
  stateAt_eq fun k hk => by rw [ofInt_natCast, readW_writeW128 _ _ _ hk, h k hk]

/-! ## The loop invariant -/

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  vars : Vars 0 s (stateAt s.mem (st s₀))

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hX : ∀ k (hk : k < 16),
      s.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hL.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_st) (by decide)]
    exact blk_word i k hk
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s hL.rsi
    (fun k hk => by rw [hL.rd, hL.wr]; exact hp.in_blk hi hk) hX hL.vars 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by rw [hR.pub .rdi (by decide), hL.rdi]
  rw [update_split, WP.block_append_iff]
  refine WP.mono (add_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂ (by rw [hR.rd, hL.rd])
    (by rw [hR.wr, hL.wr]) fun k hk => ?_) fun s₃ ⟨m₃, d₃, g₃, rd₃, wr₃⟩ => ?_
  · rw [hR.mem, stateAt_get _ _ hk, ofInt_natCast]
  rw [WP.block_append_iff]
  refine WP.mono (spread_ok s₃) fun s₄ ⟨x0, x1, x2, x3, g₄, m₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (advance_ok s₄) fun s₅ ⟨hrsi₅, hrdx₅, hzf₅, hrdi₅, x₅, m₅, rd₅, wr₅⟩ => ?_
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := hR.pub
  have hrdx : s₅.gpr .rdx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hrdx₅, g₄, g₃, pub₂ .rdx (by decide), hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hmem : s₅.mem = s.mem.writeW (st s₀) (s₃.xmm .xmm0) := by rw [m₅, m₄, m₃, hR.mem]
  have hnew : stateAt s₅.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [hmem, stateAt_writeW128 _ _ _ (Vector.zipWith (· + ·) (Spec.Md5.steps (stateAt s.mem (st s₀))
      (blk s₀ i) 64) (stateAt s.mem (st s₀))) fun k hk => by rw [d₃ k hk, Vector.getElem_zipWith],
      compressBlocks_succ, ← hL.state]
    rfl
  have hcommon : Common s₀ (i + 1) s₅ := by
    refine ⟨by rw [hrdi₅, g₄, g₃, hrdi₂], by rw [rd₅, rd₄, rd₃, hR.rd, hL.rd],
      by rw [wr₅, wr₄, wr₃, hR.wr, hL.wr], ?_, hnew⟩
    rw [hmem]
    exact hL.frame.writeW (r := stR s₀) (by simp) _ (Region.contains_self _ _)
  have hev : eval .ne s₅ = some (!(s₄.gpr .rdx - 1 == 0)) := by simp [eval, hzf₅]
  rw [← hrdx₅, hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with rsi := ?_, rdx := hrdx, vars := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₅, g₄, g₃, pub₂ .rsi (by decide), hL.rsi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hmem, stateAt_writeW128 _ _ _ #v[dword (s₃.xmm .xmm0) 0, dword (s₃.xmm .xmm0) 1,
        dword (s₃.xmm .xmm0) 2, dword (s₃.xmm .xmm0) 3]
        fun k hk => by rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl]
      simp only [vars0, x₅, x0, x1, x2, x3]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => Common s₀ (nb s₀) s' := by
  refine WP.seq (WP.mono test_ok fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  have hc₀ : Common s₀ 0 s₁ :=
    ⟨by rw [hg], hrd, hwr, by rw [hm]; exact Frame.refl _ _, by rw [hm]; rfl⟩
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    refine WP.seq (WP.mono (load_ok hp (by rw [hg]) hrd hwr) fun s₂ ⟨hv₂, hg₂, hrd₂, hwr₂, hm₂⟩ => ?_)
    have hL₀ : LInv s₀ 0 s₂ :=
      { rdi := by rw [hg₂, hg]
        rd := by rw [hrd₂, hrd]
        wr := by rw [hwr₂, hwr]
        frame := by rw [hm₂]; exact hc₀.frame
        state := by rw [hm₂]; exact hc₀.state
        rsi := by rw [hg₂, hg]; simp [blkAddr]
        rdx := by rw [hg₂, hg]; simp [nb]
        vars := by rw [hm₂]; exact hv₂ }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hL₀⟩

/-- The registers no instruction writes: the callee-saved ones, `rdi` and `rcx`. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r12, .r13, .r14, .r15, .rdi, .rcx]

theorem compress_keeps : ((instrs compress).all fun i => kept.all fun r => !Taint.clobbers i r) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem compress_keeps_reg {r : Reg} (hr : r ∈ kept) : ∀ i ∈ instrs compress, Taint.clobbers i r = false := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp compress_keeps i hi) r hr
  simpa using this

/-- `compress` meets the calling convention and its postcondition. -/
theorem correct' {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Md5.compressX86_64.post s₀ s' := by
  obtain ⟨t, s', he, hc⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (compress_keeps_reg ?_) he, ?_⟩, hc.state⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)

theorem compress_verified :
    Verified X86_64.target Impl.Md5.X86_64.Avx512.compress Proof.Md5.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct' (Proof.Md5.X86_64.pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact (Proof.Md5.X86_64.compress_verified).2.2

end VG.Proof.Md5.X86_64.Avx512
