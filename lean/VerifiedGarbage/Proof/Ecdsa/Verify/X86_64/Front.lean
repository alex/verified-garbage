import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64

/-!
# ECDSA verification on x86-64: the arguments and the key

`front_ok`: `args`, the signature's setup and tables (`stage₁`, whose
`SetupPre` the arguments meet), the load of `s` (`loadS_ok`) and ECDH's
checks of the key (`peer_ok`, `validate_ok`) leave `r`, the hash and `s` in
their slots, `R = O`, the tables of `p - 2` and `n - 2`, the flag of the
key's validity as the code checks it (`KeyOk`), and the key's point, or `G`
if it is not valid, for ECDH's ladder (`Front`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The arguments: `public = rdi` (`1 + 16 n` bytes), `digest = rsi`
(`8 n` bytes), `sig = rdx` (`16 n` bytes) and `scratch = rcx`, readable and
writable as the contract says and apart from `scratch`. -/
structure VPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 1 + 16 * c.n⟩, ⟨s.gpr .rsi, 8 * c.n⟩, ⟨s.gpr .rdx, 16 * c.n⟩]
  wr : s.wr = [⟨s.gpr .rcx, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .rdi, 1 + 16 * c.n⟩ ⟨s.gpr .rcx, size⟩
  dg_sc : Region.Disjoint ⟨s.gpr .rsi, 8 * c.n⟩ ⟨s.gpr .rcx, size⟩
  sig_sc : Region.Disjoint ⟨s.gpr .rdx, 16 * c.n⟩ ⟨s.gpr .rcx, size⟩
  sc_fit : (s.gpr .rcx).toNat + size ≤ 2 ^ 64

/-- The key's `x` and `y`, the hash, and the signature's `r` and `s`. -/
abbrev keyX (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 1) (8 * c.n))
abbrev keyY (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 (1 + 8 * c.n)) (8 * c.n))
abbrev dig (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) (8 * c.n))
abbrev sigR (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (8 * c.n))
abbrev sigS (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx + BitVec.ofNat 64 (8 * c.n)) (8 * c.n))

/-- The key is valid as the code checks it. -/
abbrev KeyOk (c : Cfg) (s₀ : State) : Prop :=
  ((s₀.mem (s₀.gpr .rdi) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s₀)) (Fin.ofNat c.C.p (keyY c s₀))

/-- After the key's checks, from the state `s₀` at entry, with the working
space at `base` and the callee-saved registers `g`. -/
structure Front (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  k : sv c base s K = sigR c s₀
  d : sv c base s D = dig c s₀
  pt : sv c base s PT = sigS c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  flag : word s.mem base (c.sl FLAG) = mask (KeyOk c s₀)
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  /-- Memory outside the working space is unchanged. -/
  unch : Unch base [(0, size)] s₀.mem s.mem

theorem args_ok (c : Cfg) (s : State) (h7 : c.n < 7) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) s fun s' =>
      s'.gpr .r8 = s.gpr .rcx ∧ s'.gpr .r9 = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rdx ∧
        s'.gpr .r10 = s.gpr .rdx + BitVec.ofNat 64 (8 * c.n) ∧
        s'.gpr .rdx = s.gpr .rdi + BitVec.ofNat 64 1 ∧ Keeps [.r8, .r9, .rcx, .r10, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Verify.X86_64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [signExtend_ofNat _ (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

theorem verify_eq' (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.verify c =
    .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (.seq (.block c.setup)
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
    (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
    (.seq (Impl.Ecdh.X86_64.Cfg.validate c) (Impl.Ecdsa.Verify.X86_64.Cfg.back c))))) := rfl

/-- Ranges of the working space, as one. -/
theorem unch_whole {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, size)] m m' :=
  (h.outside fun w hw => ⟨Nat.zero_le _, by have := hW w hw; omega⟩).unch

theorem slW_le (h7 : c.n < 7) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact sl_le c h7 (hl i hi)

theorem flag_le (h0 : 0 < c.n) (h7 : c.n < 7) : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_le c h7 (i := FLAG) (by decide)
  dsimp only; omega

/-- `args`, the signature's setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, (∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r) → Front c s₀ (s₀.gpr .rcx) g s →
      WP isa rest s Q) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (.seq (.block c.setup)
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.validate c) rest))))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hsz : size = 8192 := rfl
  refine WP.seq (WP.mono (args_ok c s₀ h7) fun s₁ ⟨r8₁, r9₁, rcx₁, r10₁, rdx₁, k₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi := k₁.1 _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    refine ⟨by rw [k₁.2.2.2, hp.wr, r8₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [r8₁]; exact hp.sc_fit⟩
    · rw [rcx₁, hrd₁, hp.rd]
      exact ⟨⟨s₀.gpr .rdx, 16 * c.n⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [rsi₁, hrd₁, hp.rd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega)⟩
    · rw [rdx₁, hrd₁, hp.rd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [rsi₁, r8₁]; exact hp.dg_sc
    · rw [rdx₁, r8₁]; exact hp.pk_sc.sub_left (Offset.sub_base _ (by omega))
    · rw [rcx₁, r8₁]; exact hp.sig_sc.sub_left (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (stage₁ hc hsp (rest := .block []) (Q := St₁ c s₁ (s₁.gpr .r8))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [r8₁] at S₂
  have hn := S₂.scr.nowrap
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  have W₂ : Outside (s₀.gpr .rcx) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.2.1 x)
  -- `s`.
  have hr10 : s₂.gpr .r10 = s₀.gpr .rdx + BitVec.ofNat 64 (8 * c.n) := by rw [S₂.gpr _ (by decide), r10₁]
  have hPT := sl_le c h7 (i := PT) (by decide)
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.loadS]
  refine WP.seq (WP.mono (loadBE_ok S₂.scr (src := .r10) (by decide) hPT (fun d hd => by
      rw [hrw₂, hp.rd, hr10, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .rdx, 16 * c.n⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hr10]
      exact (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))).sub_right
        (Offset.sub_base _ hPT))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have hs₃ := S₂.scr.of_keepRegs k₃ (by decide)
  have U₃ : Unch (s₀.gpr .rcx) (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  have F₃ := S₂.fixed.unch h7 hn (fixedOk_slW (l := [PT]) (by decide)) U₃
  have v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c (s₀.gpr .rcx) s₃ i = sv c (s₀.gpr .rcx) s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  have pt₃ : sv c (s₀.gpr .rcx) s₃ PT = sigS c s₀ := by
    rw [sv, e₃, hr10, bytesAt_keep W₂ (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))) (by omega)
      (by omega)]
  -- The key.
  have hq₃ : s₃.gpr .r9 = s₀.gpr .rdi := by rw [k₃.gpr _ (by decide), S₂.gpr _ (by decide), r9₁]
  have hrw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [k₃.rd, k₃.wr, hrw₂]
  refine WP.seq (WP.mono (peer_ok hc hs₃ hq₃ (by rw [hrw₃, hp.rd]; simp) hp.pk_sc F₃.mp)
    fun s₄ ⟨hs₄, k₄, U₄, r2₄, bp₄, y₄, f₄⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₄ i = sv c (s₀.gpr .rcx) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have W₃ : Outside (s₀.gpr .rcx) 0 size s₀.mem s₃.mem :=
    W₂.trans ((U₃.outside fun w hw => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
      exact ⟨Nat.zero_le _, hPT⟩))
  have x₄ : sv c (s₀.gpr .rcx) s₃ E = keyX c s₀ := by
    rw [v₃ (by decide) (by decide), S₂.e]
    simp only [ev, k₁.2.1, rdx₁]
  have hq0 : s₃.mem (s₀.gpr .rdi) = s₀.mem (s₀.gpr .rdi) := by
    have := keep_of_disjoint' W₃ hp.pk_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have y₄' : sv c (s₀.gpr .rcx) s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃ (hp.pk_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hf₄ : word s₄.mem (s₀.gpr .rcx) (c.sl FLAG) = mask (((s₀.mem (s₀.gpr .rdi) = 4 ∧
      sv c (s₀.gpr .rcx) s₄ E < c.C.p) ∧ sv c (s₀.gpr .rcx) s₄ QY < c.C.p)) := by
    rw [f₄, flag_unch U₃ h7 h0 hn (by decide), S₂.flag, BitVec.allOnes_and, mask_and, mask_and, hq0,
      e₄ (i := E) (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (validate_ok hc hs₄ F₄ r2₄ bp₄ hf₄)
    fun s₅ ⟨hs₅, g₅, rd₅, wr₅, U₅, f₅, px_lt, py_lt, px, py⟩ => h s₁.gpr s₅
      (fun r hr => k₁.1 r (by revert r; decide)) ?_)
  have F₅ := F₄.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₅
  have e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .rcx) s₅ i = sv c (s₀.gpr .rcx) s₄ i := fun hi hl hf =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      i ≠ PT → sv c (s₀.gpr .rcx) s₅ i = sv c (s₀.gpr .rcx) s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  have t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) = s₂.mem (off (s₀.gpr .rcx) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₄ h7 hn hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hn hj ht (tbl_apart_slW (by decide) _ t)]
  have hok : PeerOk c (s₀.gpr .rcx) s₄ ((s₀.mem (s₀.gpr .rdi) = 4 ∧ sv c (s₀.gpr .rcx) s₄ E < c.C.p) ∧
      sv c (s₀.gpr .rcx) s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, e₄ (i := E) (by decide) (by decide) (by decide), x₄, y₄']
  simp only [hok] at f₅ px py
  rw [e₄ (i := E) (by decide) (by decide) (by decide), x₄] at px
  rw [y₄'] at py
  refine ⟨hs₅, by rw [wr₅, k₄.wr, k₃.wr, S₂.wr, k₁.2.2.2], by rw [rd₅, k₄.rd, k₃.rd, S₂.rd, k₁.2.2.1], F₅,
    by rw [a₅ (i := K) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.k]
       simp only [kv, k₁.2.1, rcx₁],
    by rw [a₅ (i := D) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.d]
       simp only [dv, k₁.2.1, rsi₁],
    by rw [e₅ (i := PT) (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide), pt₃],
    by rw [a₅ (i := RX) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rx],
    by rw [a₅ (i := RY) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.ry],
    by rw [a₅ (i := RZ) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rz],
    fun t ht => by rw [t₅ (j := 1) (by decide) t ht, S₂.t₁ t ht],
    fun t ht => by rw [t₅ (j := 2) (by decide) t ht, S₂.t₂ t ht], f₅, px_lt, py_lt, px, py, ?_⟩
  have U := ((S₂.unch.trans U₃).trans U₄).trans U₅
  rw [k₁.2.1] at U
  refine unch_whole U fun w hw => ?_
  simp only [List.mem_append] at hw
  rcases hw with ((hw | hw) | (hw | hw)) | (hw | hw)
  · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
  · exact slW_le h7 (by decide) w hw
  · exact slW_le h7 (by decide) w hw
  · exact flag_le h0 h7 w hw
  · exact slW_le h7 (by decide) w hw
  · exact flag_le h0 h7 w hw

end VG.Proof.Ecdsa.Verify.X86_64
