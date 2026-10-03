import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-!
# Deterministic ECDSA on x86-64: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` in the frame and `len` bytes of
data in the frame or in `scratch` above HMAC's working space (`DataOk`),
written to the frame at `dst`: HMAC's `init` with `K` (`init_step`), the
streaming `update` on the inner state (`upd_step`), and HMAC's `finalize`
(`fin_step`), for any implementation `v` of SHA-256's compression function.
They change only HMAC's states and working space (the first 1024 bytes of
`scratch`), the 24 bytes below the frame, and `dst` (`hmac_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin
  core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)

/-- SHA-256's functions, with the compression function `v`. -/
abbrev Hv (v : Compress) : Impl.Pbkdf2.Md.X86_64.Hash := Proof.Pbkdf2.Md.X86_64.Sha256.hash v

/-- What the proofs know of them. -/
abbrev okv (v : Compress) : HashOK (Hv v) := Proof.Pbkdf2.Md.X86_64.Sha256.ok v

/-- The code, with the implementation `v` of SHA-256's compression function. -/
def cfgOf (v : Compress) : Cfg where
  H := Hv v
  n := Spec.P256.n
  tries := 8
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := Impl.Ecdsa.X86_64.signP256

section
variable (v : Compress)

theorem hI : Verified X86_64.target (Hv v).hmacInit (initG (okv v).SH (Hv v).W) :=
  hmacInit_ok (okv v) Proof.Pbkdf2.Md.X86_64.Sha256.coreOK (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    Proof.Pbkdf2.Md.X86_64.Sha256.satI

theorem hIsp : NoSp (Hv v).hmacInit :=
  nosp_of (core_hmacInit (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iNs Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hinitNs)

theorem hId : (Hv v).hmacInit.depth ≤ 2 :=
  core_hmacInit_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cD
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iD Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hinitD

theorem hF : Verified X86_64.target (Hv v).hmacFin (finG (okv v).SH (Hv v).W) :=
  hmacFin_ok (okv v) Proof.Pbkdf2.Md.X86_64.Sha256.coreOK (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    Proof.Pbkdf2.Md.X86_64.Sha256.satF

theorem hFsp : NoSp (Hv v).hmacFin :=
  nosp_of (core_hmacFin (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cNs
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hfinNs)

theorem hFd : (Hv v).hmacFin.depth ≤ 2 :=
  core_hmacFin_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cD
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hfinD

end

theorem hS (v : Compress) : (Hv v).S = 96 := rfl
theorem hW (v : Compress) : 8 * (Hv v).W = 832 := rfl
theorem hWb (v : Compress) : (okv v).stream.Wb = 608 := rfl
theorem hB (v : Compress) : (Hv v).P.B = 64 := rfl
theorem hD (v : Compress) : (Hv v).D = 32 := rfl
theorem hSs (v : Compress) : (Hv v).stream.S = 96 := rfl
theorem hDs (v : Compress) : (Hv v).stream.D = 32 := rfl

/-- Facts about the sizes of SHA-256's states and working space. -/
macro "nums" : tactic => `(tactic| first | omega | (simp only [hS, hW, hWb, hB, hD, hSs, hDs]; omega))

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk (L : Lay) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 128) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 1024 ≤ o ∧ o + len ≤ 8192)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 1024) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The data is apart from the frame's slot at `dst`. -/
theorem dst (hd : DataOk L da len) (hL : L.Ok) {d : Nat} (h₁ : 24 ≤ d) (h₂ : d + 32 ≤ 160)
    (hne : ∀ o, da = L.B + BitVec.ofNat 64 o → o + len ≤ d ∨ d + 32 ≤ o) :
    Region.Disjoint ⟨da, len⟩ ⟨L.B + BitVec.ofNat 64 d, 32⟩ := by
  rcases hd with ⟨o, rfl, h₁', h₂'⟩ | ⟨o, rfl, h₁', h₂'⟩
  · exact Offset.disjoint _ (hne o rfl) (by omega) (by omega)
  · exact (hL.stk_scr (d := d) (n := 32) (by omega) h₂').symm

theorem within (hd : DataOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Cfg.scr .rdi sInner ++ Cfg.scr .rsi sOuter ++ Cfg.fr .rdx fK ++
      ([.mov32 .rcx (.imm 32)] : List Instr) ++ Cfg.scr .r8 sWork)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .rsi = L.scr + BitVec.ofNat 64 96 ∧
      t'.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ t'.gpr .rcx = BitVec.ofNat 64 32 ∧
      t'.gpr .r8 = L.scr + BitVec.ofNat 64 192 := by
  have h128 := hc.inFr (d := 128) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.scr, Cfg.fr, sInner, sOuter, sWork, fK, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.load64, State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp,
    Offset.add_add, Nat.reduceAdd, h128, Option.some.injEq, exists_eq_left', hc.pScr, sx32,
    Nat.reducePow, Nat.reduceLT]
  exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, rfl, trivial⟩

/-- The writes of a call, within HMAC's working space and the stack below the frame. -/
theorem safe_call {u : State} (hc : Ctx L g m₀ u) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r) {n : Nat}
    (hn : n ≤ 24) : ∀ r ∈ ws ++ [below (u.gpr .rsp) n], Safe L r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hs r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr (.inr ((hc.below_sub hn).trans (Region.sub_prefix (by omega))))

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 1024⟩, ⟨L.B, 24⟩] t.mem u.mem
  inner : Spec.Sha256.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32)) Spec.Hmac.ipad)
  outer : Spec.Sha256.Repr u.mem (L.scr + BitVec.ofNat 64 96)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 1024) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 1024⟩ :=
  Offset.sub_base _ h

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 0)
    (hsi : u.gpr .rsi = L.scr + BitVec.ofNat 64 96) (hdx : u.gpr .rdx = L.B + BitVec.ofNat 64 24)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 32) (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 192) :
    Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := Hv v) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 96) (L.B + BitVec.ofNat 64 24) (L.scr + BitVec.ofNat 64 192) 32 := by
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx]; rfl, r8 := h8, klB := by nums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      i_o := Offset.disjoint _ (by nums) (by nums) (by nums)
      i_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      k_i := hL.stk_scr (by omega) (by nums)
      k_o := hL.stk_scr (by omega) (by nums)
      k_s := hL.stk_scr (by omega) (by nums)
      stk_i := by rw [hsp]; exact hL.low_scr (by nums)
      stk_o := by rw [hsp]; exact hL.low_scr (by nums)
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by omega)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; show _ + 832 ≤ _; omega }

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (Cfg.scr .rdi sInner ++ Cfg.scr .rsi sOuter ++ Cfg.fr .rdx fK ++
      ([.mov32 .rcx (.imm 32)] : List Instr) ++ Cfg.scr .r8 sWork)) (.call (Hv v).hmacInitN (Hv v).hmacInit)) t
      (Inited L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hL hc) fun u ⟨hcu, hmu, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcu.rsp, below24]
  have a := initA (v := v) hL hcu hdi hsi hdx hcx h8
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call (okv v) (hI v) (hIsp v) (hId v) a
    fun u' hrd hwr hcs hf hi ho => ?_
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, (Hv v).S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 96, (Hv v).S⟩,
      ⟨L.scr + BitVec.ofNat 64 192, 8 * (Hv v).W⟩], Region.Sub r ⟨L.scr, 1024⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  refine ⟨hcu.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hcu (fun r hr => .inr (.inl ((hsafe r hr).trans (Region.sub_prefix (by omega))))) (Nat.le_refl _)),
    hmu ▸ hf.sub fun r hr => ?_, by rw [← hmu]; exact hi, by rw [← hmu]; exact ho⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨⟨L.scr, 1024⟩, by simp, hsafe r hr⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.B, 24⟩, by simp, by rw [hsp]; exact sub_refl _⟩

/-! ## The streaming `update` -/

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = 32) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 k).length = 64 := by
  simp [Spec.Hmac.blockKey, Spec.Hmac.sha256, hk]

theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hlen : len < 2 ^ 32) :
    WP isa (.block (Cfg.scr .rdi sInner ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (Hv v).P.B))] : List Instr) ++ dataA ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ Cfg.scr .r8 sWork)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .rsi = BitVec.ofNat 64 64 ∧
      u'.gpr .rdx = da ∧ u'.gpr .rcx = BitVec.ofNat 64 len ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 192 := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (mov32_ok hL h₁.ctx (d := .rsi) (by decide) (n := 64) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (mov32_ok hL h₃.ctx (d := .rcx) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 192) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr) (len : Nat)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 1024⟩, ⟨L.B, 24⟩] t.mem u.mem
  inner : Spec.Sha256.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32))
      Spec.Hmac.ipad ++ Spec.Sha256.bytesAt t.mem da len)
  outer : Spec.Sha256.Repr u.mem (L.scr + BitVec.ofNat 64 96)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32))
      Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 128) (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hdx : w.gpr .rdx = da)
    (hcx : w.gpr .rcx = BitVec.ofNat 64 len) (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 192) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs (okv v).stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 192) len := by
  have hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega)
  exact
    { rdi := hdi, rdx := hdx, rcx := by rw [hcx, BitVec.toNat_ofNat]; omega, r8 := h8
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      st_sc := Offset.disjoint _ (by nums) (by nums) (by nums)
      d_st := hd.work hL (by nums)
      d_sc := hd.work hL (by nums)
      stk_st := (hL.low_scr (by nums)).sub_left hsp
      stk_d := (hd.low hL).sub_left hsp
      stk_sc := (hL.low_scr (by nums)).sub_left hsp }

theorem upd_step (hL : L.Ok) {t u : State} (hu : Inited L g m₀ t u) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hd : DataOk L da len)
    (hlen : len ≤ 128) :
    WP isa (.seq (.block (Cfg.scr .rdi sInner ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (Hv v).P.B))] : List Instr) ++ dataA ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 len))] : List Instr) ++ Cfg.scr .r8 sWork)) (.call (Hv v).updN (Hv v).updC)) u
      (Updated L g m₀ t da len) := by
  refine WP.seq (WP.mono (updArgs_ok (v := v) hL hu.ctx hdA (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hsp : Region.Sub (below (w.gpr .rsp) 16) ⟨L.B, 24⟩ := hcw.below_sub (by omega)
  have a := updA (v := v) hL hcw hd hlen hdi hdx hcx h8
  refine Proof.Pbkdf2.Md.X86_64.Calls.upd_call (okv v).stream a (by omega) fun w' af hr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, (Hv v).stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 192, (okv v).stream.Wb⟩], Region.Sub r ⟨L.scr, 1024⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  have hf' : Frame [⟨L.scr, 1024⟩, ⟨L.B, 24⟩] w.mem w'.mem := af.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 1024⟩, by simp, hws r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, hsp⟩
  have hdata : Spec.Sha256.bytesAt w.mem da len = Spec.Sha256.bytesAt t.mem da len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 1024) (by omega)
    · exact (hd.low hL).symm
  have hk : (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32).length = 32 := by
    simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hcw (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)),
    hu.frame.trans (hmw ▸ hf'), ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) (by rw [hsi, xorPad_length, blockKey_length hk])
  · refine (okv v).sh_reloc w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 96, 96⟩) af.frame (fun r hr => ?_) (by show (96 : Nat) ≤ 2 ^ 64; decide) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by nums) (by nums) (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.low_scr (by omega)).sub_left hsp).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {len dst : Nat} (hlen : len ≤ 128)
    (hdst : dst < 2 ^ 31) :
    WP isa (.block (Cfg.scr .rdi sInner ++ Cfg.scr .rsi sOuter ++
      ([.mov32 .rdx (.imm (BitVec.ofNat 32 ((Hv v).P.B + len)))] : List Instr) ++ Cfg.fr .rcx dst ++ Cfg.scr .r8 sWork)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .rsi = L.scr + BitVec.ofNat 64 96 ∧ u'.gpr .rdx = BitVec.ofNat 64 ((Hv v).P.B + len) ∧
        u'.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 192 := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .rsi) (by decide) (a := 96) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (mov32_ok hL h₂.ctx (d := .rdx) (by decide) (n := (Hv v).P.B + len) (by nums)) fun u₃ h₃ => ?_
  refine WP.mono (fr_ok hL h₃.ctx (d := .rcx) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := 192) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr) (len dst : Nat)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 1024⟩, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), 32⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) 32 =
    Spec.Hmac.hmac Spec.Hmac.sha256 (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32)
      (Spec.Sha256.bytesAt t.mem da len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + 32 ≤ 104)
    (hdi : w.gpr .rdi = L.scr + BitVec.ofNat 64 0) (hsi : w.gpr .rsi = L.scr + BitVec.ofNat 64 96)
    (hdx : w.gpr .rdx = BitVec.ofNat 64 ((Hv v).P.B + len)) (hcx : w.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst))
    (h8 : w.gpr .r8 = L.scr + BitVec.ofNat 64 192) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := Hv v) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 96) (BitVec.ofNat 64 ((Hv v).P.B + len)) (L.B + BitVec.ofNat 64 (24 + dst))
      (L.scr + BitVec.ofNat 64 192) := by
  have hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      i_u := Offset.disjoint _ (by nums) (by nums) (by nums)
      i_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      i_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      u_o := (hL.stk_scr (d := 24 + dst) (by nums) (by nums)).symm
      u_s := Offset.disjoint _ (by nums) (by nums) (by nums)
      o_s := hL.stk_scr (by nums) (by nums)
      stk_i := by rw [hsp]; exact hL.low_scr (by nums)
      stk_u := by rw [hsp]; exact hL.low_scr (by nums)
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by nums)
      stk_s := by rw [hsp]; exact hL.low_scr (by nums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; show _ + 832 ≤ _; omega }

theorem fin_step (hL : L.Ok) {t u : State} {da : Addr} {len dst : Nat} (hu : Updated L g m₀ t da len u)
    (hlen : len ≤ 128) (hdst : dst + 32 ≤ 104) :
    WP isa (.seq (.block (Cfg.scr .rdi sInner ++ Cfg.scr .rsi sOuter ++
      ([.mov32 .rdx (.imm (BitVec.ofNat 32 ((Hv v).P.B + len)))] : List Instr) ++ Cfg.fr .rcx dst ++ Cfg.scr .r8 sWork))
      (.call (Hv v).hmacFinN (Hv v).hmacFin)) u (Done L g m₀ t da len dst) := by
  refine WP.seq (WP.mono (finArgs_ok (v := v) hL hu.ctx hlen (by omega))
    fun w ⟨hcw, hmw, hdi, hsi, hdx, hcx, h8⟩ => ?_)
  have hsp : below (w.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hcw.rsp, below24]
  have a := finA (v := v) hL hcw (len := len) hdst hdi hsi hdx hcx h8
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call (okv v) (hF v) (hFsp v) (hFd v) a
    fun w' hrd hwr hcs hf hpost => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, (Hv v).S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (24 + dst), (Hv v).D⟩, ⟨L.scr + BitVec.ofNat 64 192, 8 * (Hv v).W⟩] ++
      [below (w.gpr .rsp) 24], ∃ r' ∈ [(⟨L.scr, 1024⟩ : Region), ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), 32⟩],
      Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 1024⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), 32⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 1024⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  have hk : (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 24) 32).length = 32 := by
    simp [Spec.Sha256.bytesAt]
  have hl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ hf.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (hs.trans (Region.sub_prefix (by omega))))
    · exact .inr (.inr (hs.trans (Region.sub_prefix (by omega))))
    · exact safe_low L (by omega) |>.elim (fun h => .inl (hs.trans h)) fun h => h.elim
        (fun h => .inr (.inl (hs.trans h))) fun h => .inr (.inr (hs.trans h))
  · exact hpost _ _ (blockKey_length hk) (by rw [blockKey_length hk, hl]; omega)
      (hmw ▸ hu.inner) (by rw [hl]) (hmw ▸ hu.outer)

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hd : DataOk L da len)
    (hlen : len ≤ 128) (hdst : dst + 32 ≤ 104) :
    WP isa ((cfgOf v).hmac dataA len dst) t (Done L g m₀ t da len dst) :=
  seq_seq (init_step hL hc) fun _ hu => seq_seq (upd_step hL hu hdA hd hlen) fun _ hw =>
    fin_step hL hw hlen hdst

end VG.Proof.Ecdsa.Rfc6979.X86_64
