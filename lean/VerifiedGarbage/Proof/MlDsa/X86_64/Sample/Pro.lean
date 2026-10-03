import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-!
# ML-DSA on x86-64: the sampling functions' prologue and epilogue

The prologue (`pro`) saves `rbx`, `rbp` and `r12` in the working space and
sets up the layout: from what running it leaves, `J0` holds (`pro_J0`). The
epilogue (`epi`) restores them: with `Env`, the calling convention's
obligations hold at the end (`epi_ok`). A coefficient store of a loop (`[rbp +
4 rdi]`) is apart from everything `Env` keeps (`ea_aJ`, `Env.store`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample (coeffAddr polyR coeff_contains)
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- A word of the working space, in the regions of the entry state. -/
theorem inScrσ {a n : Nat} (h : a + n ≤ 2048) : InRegions σ.wr (P.at' a) n := by
  rw [hp.wr]
  exact ⟨P.scrR, by simp, contains_scr h⟩

omit hp in
/-- What running the prologue leaves: `J0`. -/
theorem pro_J0 {s : State}
    (hm : s.mem = ((σ.mem.writeW (P.at' 2024) (σ.gpr .rbx)).writeW (P.at' 2032) (σ.gpr .rbp)).writeW
      (P.at' 2040) (σ.gpr .r12))
    (hbx : s.gpr .rbx = P.scr) (hbp : s.gpr .rbp = P.a) (h12 : s.gpr .r12 = P.prm) (hcx : s.gpr .rcx = P.sd)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 P.len) (hk : Keep [.rbx, .rbp, .r12, .rcx, .r8] σ s) : J0 P σ s := by
  have sep : ∀ a b, 2024 ≤ a → a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inl h2) (by omega) (by omega)
  have sep' : ∀ a b, 2024 ≤ b → b + 8 ≤ a → a + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inr h2) (by omega) (by omega)
  have hin : ∀ a, a + 8 ≤ 2048 → P.scrR.Contains (P.at' a) (64 / 8) := fun a ha => contains_scr ha
  refine ⟨⟨hk.2.1, hk.2.2, hbx, hbp, h12, hk.gpr (by decide), fun r hr => hk.gpr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide), ?_, ?_⟩, hcx, h8⟩
  · rw [hm, Mem.readW_writeW_sep (sep 2024 2040 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 2024 2032 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 2032 2040 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_self64]
    exact ⟨rfl, rfl, rfl⟩
  · rw [hm]
    exact (((Frame.refl _ _).writeW (by simp) _ (hin 2024 (by omega))).writeW (by simp) _
      (hin 2032 (by omega))).writeW (by simp) _ (hin 2040 (by omega))

/-- The epilogue: `rbx`, `rbp` and `r12` restored. -/
theorem epi_ok {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => (s'.gpr .rbx = σ.gpr .rbx ∧ s'.gpr .rbp = σ.gpr .rbp ∧
      s'.gpr .r12 = σ.gpr .r12 ∧ s'.mem = s.mem) ∧ Keep [.rbp, .r12, .rbx] s s' := by
  refine WP.keep _ ?_ (by decide)
  have e := he.saved
  unfold epi
  xrun [he.rbx, inScrRd hp he (a := 2024) (n := 8) (by omega), inScrRd hp he (a := 2032) (n := 8) (by omega),
    inScrRd hp he (a := 2040) (n := 8) (by omega), e.1, e.2.1, e.2.2]

omit hp in
theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 16) :=
  (Offset.base_disjoint_below sp (n := 16) (k := 8) (by omega))

/-- The calling convention's obligations, at the end of a sampling function:
the callee-saved registers restored and the return address not written. -/
theorem gpr_end {s s' : State} (he : Env P σ s) (hbx : s'.gpr .rbx = σ.gpr .rbx) (hbp : s'.gpr .rbp = σ.gpr .rbp)
    (h12 : s'.gpr .r12 = σ.gpr .r12) (hk : Keep [.rax, .rbp, .r12, .rbx] s s') (hm : s'.mem = s.mem) :
    gprPreserved σ s' := by
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact hbp
    · rw [hk.gpr (by decide), he.rsp]
    · exact h12
    all_goals rw [hk.gpr (by decide)]; exact he.cs _ (by decide)
  · rw [hm]
    exact he.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, ret_below _⟩) (by decide)

omit hp in
theorem retJ_ok (s : State) :
    WP isa (.block retJ) s fun s' => (s'.gpr .rax = s.gpr .rdi >>> 8 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold retJ
  xrun

omit hp in
theorem ret_val {x : BitVec 64} {j : Nat} (hx : x = BitVec.ofNat 64 j) (hj : j ≤ 256) :
    (x >>> 8).setWidth 32 = if j = 256 then 1 else 0 := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, shr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)]
  split
  · subst j; rfl
  · rw [Nat.div_eq_of_lt (by omega)]; rfl

/-- The end of a sampling function that returns whether `j` (in `rdi`) is 256. -/
theorem retEpi_ok {s : State} (he : Env P σ s) {j : Nat} (hdi : s.gpr .rdi = BitVec.ofNat 64 j) (hj : j ≤ 256) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      (s'.gpr .rax).setWidth 32 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ gprPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (retJ_ok s) fun s1 ⟨⟨hax, hm1⟩, k1⟩ => ?_
  have he1 := he.keep hm1 (k1.mono (by decide))
  refine WP.mono (epi_ok hp he1) fun s2 ⟨⟨hbx, hbp, h12, hm2⟩, k2⟩ =>
    ⟨by rw [k2.gpr (by decide), hax, ret_val hdi hj], by rw [hm2, hm1], ?_⟩
  exact gpr_end hp he hbx hbp h12 ((k1.trans k2).mono (rs' := [.rax, .rbp, .r12, .rbx]) (by simp)) (hm2.trans hm1)

end

/-! ## Stores to the output polynomial -/

/-- `a[j]`, with `rbp` = `a` and `rdi` = `j`. -/
theorem ea_aJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 j) :
    s.ea aJ = coeffAddr aP j := by
  simp only [State.ea, aJ, hbp, hdi]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ofNat64_succ {j : Nat} (_h : j + 1 < 2 ^ 64) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat64_toNat {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem offAdd (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- An offset of an offset of the working space. -/
theorem at_add (P : Sp) (a b : Nat) : P.at' a + BitVec.ofNat 64 b = P.at' (a + b) := offAdd _ _ _

theorem sx256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

/-- `cmp rdi, 256`: CF is `rdi < 256`. -/
theorem cmpRdi_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [sx256, show (256 : BitVec 64).toNat = 256 from rfl]

/-- `add rsi, k; sub rcx, 1`: the step of a loop. -/
theorem step_ok (s : State) (k : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm k), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi + k.signExtend 64 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun

end VG.Proof.MlDsa.X86_64.Sample
