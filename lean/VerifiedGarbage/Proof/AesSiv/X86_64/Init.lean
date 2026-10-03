import VerifiedGarbage.Proof.AesSiv.X86_64.Common

/-!
# AES-SIV on x86-64: `vg_aes_siv_init`

The code saves `rbx`, `rbp` and `r12`–`r14` in the working space, expands
`K1` into the context, derives its subkeys after the schedule, expands `K2`
after them and restores the registers: the context is then that of the key
(`Spec.Siv.KeyRepr`). The code between the calls is constant time by the
taint analysis, and the calls by their own proofs (`ek_rel`, `sub_rel`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel toNat_ofNat
  toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the working space `S`. -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) : Prop where
  rdi : s₀.gpr .rdi = Kp
  rsi : (s₀.gpr .rsi).toNat = KL
  rdx : s₀.gpr .rdx = Ct
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, ⟨S, 2560⟩]
  k_c : (⟨Kp, KL⟩ : Region).Disjoint ⟨Ct, 512⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  c_s : (⟨Ct, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Ct, 512⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2560⟩
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨Ct, 512⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : Ct.toNat + 512 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 1 = BitVec.ofNat 64 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 3 + BitVec.signExtend 64 (BitVec.ofNat 32 6) = BitVec.ofNat 64 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem IPre.rounds {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 (KL / 2) ∧
      s₁.gpr .rdx = Ct ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 256 ∧ s₁.gpr .rbx = Kp ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 2) ∧ s₁.gpr .r12 = Ct ∧ s₁.gpr .r13 = S ∧
      s₁.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .rsi = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rsi, toNat_ofNat (by rcases hp.klen with h | h | h <;> omega)])
  have hrun := Spill.save_run .rcx initSaved s₀ (fun p hp' => by
    simp only [initSaved, saveOff, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [hp.rcx]
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> exact inS _ (by decide))
  refine ⟨_, by
    rw [initPre, show saveCode .rcx initSaved = Spill.saveCode .rcx initSaved from rfl, runBlock_append,
      hrun, Option.bind_some]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, execShift, imm, csOff, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      gpr_setFlags, ite_true, ite_false]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, ite_true, ite_false, hp.rdi, hp.rdx, hp.rcx, hKL, half_bv hp.klen, rounds_bv hp.klen,
    sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r hr hn => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [initSaved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp Ct (S + BitVec.ofNat 64 256) (KL / 2)
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IPre.sS {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ 2560) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2560⟩ :=
  Offset.sub_base S (by omega)

theorem IPre.sC {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ 512) : Region.Sub ⟨Ct + BitVec.ofNat 64 d, n⟩ ⟨Ct, 512⟩ :=
  Offset.sub_base Ct (by omega)

theorem IPre.sK {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (_hp : IPre s₀ Kp Ct S KL) {d n : Nat}
    (h : d + n ≤ KL) : Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega)

/-- The arguments of a call of `vg_aes_expand_key` on half the key, from
offset `a` (0 or `KL / 2`), into the context at offset `c`. -/
theorem IPre.eargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) {a c : Nat}
    (ha : a + KL / 2 ≤ KL) (hc : c + 240 ≤ 512)
    (rdi : s.gpr .rdi = Kp + BitVec.ofNat 64 a) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 2))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 c) (rcx : s.gpr .rcx = S + BitVec.ofNat 64 256)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    EArgs s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) (S + BitVec.ofNat 64 256) (KL / 2) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  klen := hp.half
  kw := (hp.k_c.sub_left (hp.sK ha)).sub_right (hp.sC hc)
  ks := (hp.k_s.sub_left (hp.sK ha)).sub_right (hp.sS (by decide))
  ws := (hp.c_s.sub_left (hp.sC hc)).sub_right (hp.sS (by decide))
  stkK := by rw [rsp]; exact hp.stk_k.sub_right (hp.sK ha)
  stkW := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC hc)
  stkS := by rw [rsp]; exact hp.stk_s.sub_right (hp.sS (by decide))
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Kp, KL⟩, by simp, a, rfl, by simp; omega⟩
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ Kp Ct S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ :=
    initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩
  have := hp.eargs (s := s₁) (a := 0) (c := 0) (by omega) (by decide) (by rw [rdi₁, k0]) rsi₁
    (by rw [rdx₁, k0]) rcx₁ rsp₁ rd₁ wr₁
  rwa [k0, k0] at this

/-! ## Between the calls -/

theorem initMid₁_ok {s : State} {Ct S : Addr} {R : Nat} (h12 : s.gpr .r12 = Ct) (h13 : s.gpr .r13 = S)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid₁ s = some s' ∧ s'.gpr .rdi = Ct ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = Ct + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₁, imm, csOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h12, h13, h14,
    sx_ofNat (show 240 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem initMid₂_ok {s : State} {Kp Ct S : Addr} {H : Nat} (hb : s.gpr .rbx = Kp)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 H) (h12 : s.gpr .r12 = Ct) (h13 : s.gpr .r13 = S) :
    ∃ s', runBlock isa initMid₂ s = some s' ∧ s'.gpr .rdi = Kp + BitVec.ofNat 64 H ∧
      s'.gpr .rsi = BitVec.ofNat 64 H ∧ s'.gpr .rdx = Ct + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = S + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₂, imm, csOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hb, hbp, h12, h13,
    sx_ofNat (show 272 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (rdi : s.gpr .rdi = Ct) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 8 + 6))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 240) (rcx : s.gpr .rcx = S + BitVec.ofNat 64 256)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  rounds := hp.rounds
  wk := Offset.base_disjoint Ct (by decide) (by have := hp.wC; omega)
  ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (hp.sS (by decide))
  ks := (hp.c_s.sub_left (hp.sC (by decide))).sub_right (hp.sS (by decide))
  stkW := by rw [rsp]; exact hp.stk_c.sub_right (Region.sub_prefix (by decide))
  stkK := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC (by decide))
  stkS := by rw [rsp]; exact hp.stk_s.sub_right (hp.sS (by decide))
  wrapK := by rw [toNat_add_lt Ct hp.wC (by decide)]; have := hp.wC; omega
  wrapS := by rw [toNat_add_lt S hp.wS (by decide)]; have := hp.wS; omega
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩

/-! ## The key context -/

theorem take_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).take a = Spec.Aes.bytesAt m p a := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem drop_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-- The context `init` leaves is that of the key: the schedule of `K1`, its
subkeys and the schedule of `K2`, each where the calls left it. -/
theorem keyRepr_of {m m₀ : Mem} {Ct Kp : Addr} {KL : Nat} (hl : KL = 32 ∨ KL = 48 ∨ KL = 64)
    (h1 : Spec.Aes.bytesAt m Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2)))
    (hs : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).2)
    (h2 : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 272) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2))) :
    Spec.Siv.KeyRepr m Ct (Spec.Aes.bytesAt m₀ Kp KL) := by
  have hKL : KL = KL / 2 + KL / 2 := by omega
  have hlen := Proof.Cmac.bytesAt_length m₀ Kp KL
  have e8 : KL / 8 = KL / 2 / 4 := by omega
  have k1 : (Spec.Aes.bytesAt m₀ Kp KL).take (KL / 2) = Spec.Aes.bytesAt m₀ Kp (KL / 2) := by
    have := take_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have k2 : (Spec.Aes.bytesAt m₀ Kp KL).drop (KL / 2) =
      Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2) := by
    have := drop_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have hs' : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      Spec.Aes.bytesAt m (Ct + 240) 16 ++ Spec.Aes.bytesAt m (Ct + 256) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add]; rfl
  have ka : Spec.Cmac.aes (Spec.Aes.bytesAt m₀ Kp (KL / 2)) =
      Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))) := by
    rw [Spec.Cmac.aes, Proof.Cmac.bytesAt_length, Spec.Aes.rounds, e8]
  rw [hs', ← ka] at hs
  obtain ⟨hs1, hs2⟩ := List.append_inj hs (by
    rw [Proof.Cmac.bytesAt_length, Spec.Cmac.aes]; exact (Proof.Cmac.subkeys_aes_length _ _).symm)
  refine ⟨by rw [hlen]; exact hl, ?_, ?_, ?_, ?_⟩
  · rw [hlen, k1, e8]; exact h1
  · rw [hlen, k1]; exact hs1
  · rw [hlen, k1]; exact hs2
  · rw [hlen, k2, e8]; exact h2

/-! ## The whole function -/

theorem initSaved_slots : Spill.Slots initSaved := by decide

theorem initSaved_le : ∀ p ∈ initSaved, p.2 + 8 ≤ 256 := by decide

theorem initRestored_sub : ∀ p ∈ initRestored, p ∈ initSaved := by decide

theorem initRestored_fst {r : Reg} (h : r ∉ initRestored.map Prod.fst) : r ∉ initSaved.map Prod.fst := by
  intro h'; apply h
  simp only [initSaved, initRestored, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h' ⊢
  rcases h' with h' | h' | h' | h' | h' <;> simp [h']

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .rdi = Kp at hp
  generalize s₀.gpr .rdx = Ct at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rsi).toNat = KL at hp
  have hwC := hp.wC
  have hwS := hp.wS
  have hwK := hp.wK
  have hH := hp.half
  have cs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, g₃, m₃, rd₃, wr₃⟩ := initMid₁_ok (s := s₂)
    (by rw [g₂ _ (cs _ (by simp)), h₁.r12]) (by rw [g₂ _ (cs _ (by simp)), h₁.r13])
    (by rw [g₂ _ (cs _ (by simp)), h₁.r14])
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [g₃ _ (cs _ (by simp)), g₂ _ (cs _ (by simp)), h₁.rsp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₂.rd, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₂.wr, h₁.wr]
  refine WP.seq (WP.mono (sub_call v _ (hp.sargs rdi₃ rsi₃ rdx₃ rcx₃ rsp₃ rd₃' wr₃')) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₁.gpr r := by rw [h₄.saved r hr, g₃ r hr, g₂ r hr]
  obtain ⟨s₅, run₅, rdi₅, rsi₅, rdx₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := initMid₂_ok (s := s₄)
    (by rw [g₄ _ (cs _ (by simp)), h₁.rbx]) (by rw [g₄ _ (cs _ (by simp)), h₁.rbp])
    (by rw [g₄ _ (cs _ (by simp)), h₁.r12]) (by rw [g₄ _ (cs _ (by simp)), h₁.r13])
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [g₅ _ (cs _ (by simp)), g₄ _ (cs _ (by simp)), h₁.rsp]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  refine WP.seq (WP.mono (ek_call v (hp.eargs (a := KL / 2) (c := 272) (by omega) (by decide) rdi₅ rsi₅ rdx₅
    rcx₅ rsp₅ rd₅' wr₅')) fun s₆ h₆ => ?_)
  have g₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₁.gpr r := by rw [h₆.saved r hr, g₅ r hr, g₄ r hr]
  have r13₆ : s₆.gpr .r13 = S := by rw [g₆ _ (cs _ (by simp)), h₁.r13]
  -- The memory, call by call.
  have f₁ : Frame [⟨S, 2560⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_frame_base _ _ _ _ (fun p hp' => by have := initSaved_le p hp'; omega)
      (by decide)
  have f₂ : Frame [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; exact h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₃.mem s₄.mem := by
    rw [← rsp₃]; exact h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩, below (s₀.gpr .rsp) 16]
      s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  -- The saved registers.
  have dSv {d : Nat} (hd : d + 8 ≤ 256) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
      below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
      ⟨Ct + BitVec.ofNat 64 272, 240⟩]) : (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2560⟩ := hp.sS (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact hp.stk_s.symm.sub_left sub
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved s₁.mem S s₀.gpr initSaved := by
    rw [h₁.mem]; exact Spill.saveMem_saved _ _ _ _ initSaved_slots
  have sv₆ : Spill.Saved s₆.mem S s₀.gpr initSaved := by
    refine ((sv₁.frame f₂ fun p hp' r hr => dSv (initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (m' := s₄.mem) (by rw [← m₃]; exact f₄) fun p hp' r hr => dSv (initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (by rw [← m₅]; exact f₆) fun p hp' r hr => dSv (initSaved_le p hp') r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)
  have inR : ∀ p ∈ initRestored, InRegions (s₆.rd ++ s₆.wr) (Spill.slot (s₆.gpr .r13) p.2) 8 := by
    intro p hp'
    have := initSaved_le p (initRestored_sub p hp')
    rw [r13₆, h₆.rd, h₆.wr, rd₅', wr₅', hp.wr]
    exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (Spill.restore_ok .r13 initRestored s₀.gpr s₆ (by decide) inR
    (by rw [r13₆]; exact fun p hp' => sv₆ p (initRestored_sub p hp'))) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hm : r ∈ initRestored.map Prod.fst
    · exact h₇a r hm
    · rw [h₇b r hm, g₆ r hr, h₁.other r hr (initRestored_fst hm)]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have dR (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
        below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
        ⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 2560⟩]) : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp.ret_c.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_s.sub_right (hp.sS (by decide))
      · exact Offset.base_disjoint_below _ (by decide)
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_s.sub_right (hp.sS (by decide))
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_s
    rw [m₇, f₆.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₅,
      f₄.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₃,
      f₂.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide),
      f₁.readW c (fun r hr => dR r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)]
  · show Spec.Siv.KeyRepr s₇.mem (s₀.gpr .rdx) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    rw [hp.rdx, hp.rdi, hp.rsi, m₇]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S + BitVec.ofNat 64 256, 512⟩,
        below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 256, 2176⟩,
        ⟨S, 2560⟩]) : (⟨Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
      · exact (hp.stk_k.sub_right sub).symm
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
      · exact hp.k_s.sub_left sub
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega), m₃,
        bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega),
        bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)]
    have key₁ : Spec.Aes.bytesAt s₁.mem Kp (KL / 2) = Spec.Aes.bytesAt s₀.mem Kp (KL / 2) := by
      have := bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega) r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)
      rwa [k0] at this
    have key₂ := key (a := KL / 2) (by omega)
    have sch : Spec.Aes.bytesAt s₂.mem Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp (KL / 2)) := by rw [h₂.out, key₁]
    refine keyRepr_of hp.klen ?_ ?_ ?_
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega), m₅,
        bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega), m₃, sch]
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint Ct (by omega) (by omega) (by omega)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right (hp.sS (by decide))
          · exact (hp.stk_c.sub_right (hp.sC (by decide))).symm) (by decide), m₅, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega, sch]
    · rw [h₆.out, key₂]

/-! ## Constant time -/

/-- What each call leaves for the code after it: the registers that hold
the arguments of the next one. -/
structure IAfter (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IAfter.keep {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : IAfter s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    IAfter s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.rsp],
    by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.after {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : IMid₁ s₀ Kp Ct S KL s) :
    IAfter s₀ Kp Ct S KL s :=
  ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.rsp, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' =>
      SArgs s' Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧ IAfter s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := initMid₁_ok h.r12 h.r13 h.r14
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.sargs rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'⟩

/-- The arguments of the second call of `vg_aes_expand_key`, and the
registers the code after it uses. -/
abbrev IEk (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop :=
  EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) (S + BitVec.ofNat 64 256) (KL / 2) ∧
    s.gpr .r13 = S ∧ s.gpr .rsp = s₀.gpr .rsp

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' =>
      IEk s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := initMid₂_ok h.rbx h.rbp h.r12 h.r13
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.eargs (by omega) (by decide) rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'.r13, h'.rsp⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initX86_64.pre s₀) (h0' : initX86_64.pre s₀')
    (hq : initX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .rdi = Kp at hp hp'
  generalize s₀.gpr .rdx = Ct at hp hp'
  generalize s₀.gpr .rcx = S at hp hp'
  generalize (s₀.gpr .rsi).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block initMid₁)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block initMid₂)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have agree (a b : State) (h : IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) :
      taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) a b := by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.rbx, h.2.rbx]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.r13, h.2.r13]
    · rw [h.1.r14, h.2.r14]
    · rw [h.1.rsp, h.2.rsp, q1]
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := IMid₁ s₀ Kp Ct S KL) (F₂ := IMid₁ s₀' Kp Ct S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have e₁ := (ek_rel v (P := fun a b => IMid₁ s₀ Kp Ct S KL a ∧ IMid₁ s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.args, h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL) fun a b h =>
      ⟨WP.mono (ek_call v h.1.args) fun _ h₂ => h.1.after.keep h₂.saved h₂.rd h₂.wr,
        WP.mono (ek_call v h.2.args) fun _ h₂ => h.2.after.keep h₂.saved h₂.rd h₂.wr⟩
  have m₁ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hB).wp
    (F₁ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      IAfter s₀ Kp Ct S KL s)
    (F₂ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      IAfter s₀' Kp Ct S KL s)
    fun a b h => ⟨initMid₁_wp hp h.1, initMid₁_wp hp' h.2⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (SArgs a Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧
      IAfter s₀ Kp Ct S KL a) ∧
      SArgs b Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) ∧ IAfter s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.1, h.2.1, by rw [h.1.2.rsp, h.2.2.rsp, q1]⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (sub_call v _ h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.rd h₂.wr,
      WP.mono (sub_call v _ h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.rd h₂.wr⟩
  have m₂ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hC).wp
    (F₁ := IEk s₀ Kp Ct S KL) (F₂ := IEk s₀' Kp Ct S KL)
    fun a b h => ⟨initMid₂_wp hp h.1, initMid₂_wp hp' h.2⟩
  have e₂ := (ek_rel v (P := fun a b => IEk s₀ Kp Ct S KL a ∧ IEk s₀' Kp Ct S KL b)
    fun a b h => ⟨_, _, _, _, h.1.1, h.2.1, by rw [h.1.2.2, h.2.2.2, q1]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r13 = S) (F₂ := fun (s : State) => s.gpr .r13 = S)
    fun a b h => ⟨WP.mono (ek_call v h.1.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.1.2.1],
      WP.mono (ek_call v h.2.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.2.2.1]⟩
  have p := RelCT.taint (A := taint) (P := fun a b => a.gpr .r13 = S ∧ b.gpr .r13 = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
end VG.Proof.AesSiv.X86_64
