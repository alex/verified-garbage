import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# AES-GCM on x86-64: the functions called

Untrusted: everything here is checked by Lean. What the AES-GCM functions
need of the implementations of `vg_ghash`, `vg_aes_expand_key` and
`vg_aes_ctr32` they call (`GhashImpl`, `KeyImpl`, and the existing
`Ctr32Impl`), and each call from its callee's contract (with `WP.call`), with
the regions it is given: what it needs (`GhCall`, `CtrCall`, `KeyCall`) and
what it leaves (`GhPost`, `CtrPost`, `KeyPost`); and that it is constant time
(`gh_rel`, `ctr_rel`, `key_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- An implementation of `vg_ghash` on x86-64. -/
structure GhashImpl where
  fn : Fn
  depth : fn.code.depth = 0
  ok : ∀ s, Proof.Gcm.ghashX86_64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86_64.post s s'
  ct : ConstantTime isa Proof.Gcm.ghashX86_64.pre Proof.Gcm.ghashX86_64.pub fn.code
  nosp : NoSp fn.code
  mxcsr : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : fn.code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

/-- An implementation of `vg_aes_expand_key` on x86-64. -/
structure KeyImpl where
  fn : Fn
  depth : fn.code.depth = 0
  ok : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub fn.code
  nosp : NoSp fn.code
  mxcsr : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : fn.code.all (fun i => !isa.writesSp i) = true
  features : List String

theorem nosp_of {c : Prog isa} (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.X86_64.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.ghash_correct
  ct := Proof.Gcm.X86_64.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86_64.Pclmul.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.Pclmul.ghash_correct
  ct := Proof.Gcm.X86_64.Pclmul.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

end GhashImpl

namespace KeyImpl

/-- `vg_aes_expand_key`, in the baseline ISA. -/
def scalar : KeyImpl where
  fn := ⟨"vg_aes_expand_key", Impl.Aes.X86_64.expandKey⟩
  depth := by lit_decide
  ok := Proof.Aes.X86_64.expandKey_correct
  ct := Proof.Aes.X86_64.expandKey_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  features := []

/-- `vg_aes_expand_key_aesni`. -/
def aesni : KeyImpl where
  fn := ⟨"vg_aes_expand_key_aesni", Impl.Aes.X86_64.AesNi.expandKey⟩
  depth := by lit_decide
  ok s hs := Proof.Aes.X86_64.AesNi.Key.expandKey_correct s
    ⟨hs.1, hs.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp :=
    Proof.Aes.X86_64.AesNi.Key.expandKey_ct s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨h₁.1, h₁.2.1, h₁.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2⟩ ⟨h₂.1, h₂.2.1, h₂.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2⟩
      ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  features := ["aes"]

end KeyImpl

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem disj_below {s : State} {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, n⟩) :
    ∀ r ∈ [below (s.gpr .rsp) 8], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`. -/
structure GhCall (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = H
  rsi : s.gpr .rsi = Y
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  n_lt : 16 * n < 2 ^ 64
  hy : (⟨H, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  hs : (⟨H, 16⟩ : Region).Disjoint ⟨S, 256⟩
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ys : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 256⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 256⟩
  stkH : (below (s.gpr .rsp) 8).Disjoint ⟨H, 16⟩
  stkY : (below (s.gpr .rsp) 8).Disjoint ⟨Y, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 256⟩
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨S, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n)

theorem GhCall.pre {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    Proof.Gcm.ghashX86_64.pre (s.callEntry.withRegions [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hn]
  exact ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, h.stkY, h.stkS⟩

theorem gh_call (g : GhashImpl) {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa (.call g.fn.name g.fn.code) s (GhPost s H Y D S n) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  refine WP.call (k := Proof.Gcm.ghashX86_64) g.ok g.nosp (by rw [g.depth]; decide)
    (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [g.depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hn, hm₂] at hpost
  have fE := callEntry_frame s
  rw [hpost, blockAt_frame fE (disj_below h.stkH), blockAt_frame fE (disj_below h.stkY),
    blocksAt_frame fE (disj_below h.stkD) (by have := h.n_lt; omega)]

theorem gh_rel (g : GhashImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : Addr, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call g.fn.name g.fn.code) fun _ _ => True := by
  refine RelCT.callEx g.ok g.ct fun s₁ s₂ hp => ?_
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  toNat_ofNat_lt (by omega)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.stkC, h.stkD, h.stkS, h.wrap,
    h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata hctr
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  rw [blockAt_frame fE (disj_below h.stkC), blocksAt_frame fE (disj_below h.stkD) (by have := h.wrap; omega),
    eK] at hdata
  rw [blockAt_frame fE (disj_below h.stkC)] at hctr
  exact ⟨hrd, hwr, hcs, by simpa using hf, hdata, hctr⟩

theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : Addr) (L : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 L
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  kc : (⟨K, L⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, L⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 240⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨K, L⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyPost (s : State) (K C S : Addr) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (L / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L)

theorem KeyCall.pre {s : State} {K C S : Addr} {L : Nat} (h : KeyCall s K C S L) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨K, L⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  have hL := toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hL]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.stkC, h.stkS, h.len⟩

theorem key_call (k : KeyImpl) {s : State} {K C S : Addr} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (.call k.fn.name k.fn.code) s (KeyPost s K C S L) := by
  have hL := toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) k.ok k.nosp (by rw [k.depth]; decide)
    (rd := [⟨K, L⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [k.depth] at hf
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hL, hm₂] at hpost
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  rw [hpost, bytesAt_frame (callEntry_frame s) (disj_below h.stkK)
    (by rcases h.len with rfl | rfl | rfl <;> decide)]

theorem key_rel (k : KeyImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S : Addr, ∃ L : Nat,
      KeyCall s₁ K C S L ∧ KeyCall s₂ K C S L ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call k.fn.name k.fn.code) fun _ _ => True := by
  refine RelCT.callEx k.ok k.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, S, L, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## The implementations, together -/

/-- What an AES-GCM function calls: an implementation of `vg_aes_ctr32`, the
`vg_aes_expand_key` for the same CPUs, and one of `vg_ghash`. -/
structure GcmImpl where
  ctr : Ctr32Impl
  key : KeyImpl
  gh : GhashImpl

namespace GcmImpl

variable (v : GcmImpl)

def callees : Callees := ⟨⟨v.ctr.callee.name, v.ctr.callee.code⟩, v.key.fn, v.gh.fn⟩

/-- What the names of the functions calling `vg_ghash` end with. -/
def suffix : String := v.ctr.suffix ++ v.gh.suffix

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`. -/
def features : List String := (v.ctr.features ++ v.gh.features).dedup

end GcmImpl

end VG.Proof.AesGcm.X86_64
