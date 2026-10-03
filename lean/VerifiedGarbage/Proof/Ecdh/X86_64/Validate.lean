import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages

/-!
# ECDH on x86-64: the peer's point, `[d]P` and `Z^(p-2)`

## The peer's point

`validate` takes the peer's `x` and `y` into Montgomery's form
(multiplications by `R² mod p`), computes `y² - (x³ + a x + b)` (`curveOps`,
a field program, by `fprog_ok`), ands the mask of its being zero into the
flag, and selects for the ladder the peer's point if the flag is set, else
`G` (`validate_ok`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- `curveOps` on slot numbers. -/
def curveN : List FOp :=
  [.mul W0 QYM QYM, .mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1,
    .add W2 W3 BP, .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : Impl.Ecdh.X86_64.Cfg.curveOps c = curveN.map (FOp.rename c.sl) := rfl

theorem curveN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps curveN e W1 = e QYM * e QYM - ((e QXM * e QXM * e QXM + e AP * e QXM) + e BP) := by
  simp only [curveN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W0, W1, W2, W3, QYM, QXM, AP, BP, KM, TT, SM, RM, XM, X, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem curveN_reads : readsOk curveN [QXM, QYM, AP, BP] = true := by decide

/-- The slots of the check. -/
abbrev curveSl : List Nat := [QXM, QYM, AP, BP, W0, W1, W2, W3]

theorem curveN_slots : ∀ op ∈ curveN, ∀ x ∈ op.out :: op.ins, x ∈ curveSl := by decide

theorem curveN_out : ∀ op ∈ curveN, op.out ∈ [W0, W1, W2, W3, TMP] := by decide

/-! ## Montgomery's form -/

/-- What the two multiplications by `R² mod p` leave. -/
structure MontPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, QYM, TMP]) s.mem s'.mem
  mod : ModOk c.MP' size c.C.p s'.mem base
  x_lt : sv c base s' QXM < c.C.p
  x : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E)
  y_lt : sv c base s' QYM < c.C.p
  y : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY)

theorem mont_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOk c.MP' size c.C.p s.mem base) (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (.block (Impl.Mont.X86_64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P) ++
      Impl.Mont.X86_64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P))) s (MontPost c base s) := by
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  rw [WP.block_append_iff]
  refine WP.mono (slMul_ok (MP'_n c) h7 hs hM (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega))) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have r2₁ : sv c base s₁ R2P = sv c base s R2P := sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have y₁ : sv c base s₁ QY = sv c base s QY := sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (o := QYM) (a := QY) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [r2₁, hr2']; exact Nat.mod_lt _ (by omega))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
  have x₂ : sv c base s₂ QXM = sv c base s₁ QXM := sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  refine ⟨k₂.scr hs₁, fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], by rw [k₂.rd, k₁.rd],
    by rw [k₂.wr, k₁.wr], ?_, kP₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide),
    by rw [x₂]; exact lt₁, ?_, lt₂, ?_⟩
  · exact ((unch_slots (MP'_n c) rfl k₁.unch (l := [QXM, QYM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [QXM, QYM, TMP]) (by simp) (by simp))).mono
      fun w hw => by simp only [List.mem_append, or_self] at hw; exact hw
  · rw [x₂]; exact toM_r2 hpR (by rw [e₁, hr2'])
  · exact toM_r2 hpR (by rw [e₂, r2₁, y₁, hr2'])

/-! ## The curve's equation -/

/-- `y² = x³ + a x + b`, in `Fin p`. -/
abbrev OnCurve (c : Cfg) (x y : Fe c.C) : Prop :=
  y * y - ((x * x * x + Fin.ofNat c.C.p c.C.a * x) + Fin.ofNat c.C.p c.C.b) = 0

theorem curve_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOk c.MP' size c.C.p s.mem base) (hx : sv c base s QXM < c.C.p) (hy : sv c base s QYM < c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (.block (fprog c.MP' (Impl.Ecdh.X86_64.Cfg.curveOps c) ++
      Impl.Ecdh.X86_64.Cfg.checkZero c (c.sl W1))) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [W0, W1, W2, W3, TMP] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (P₀ ∧ OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM))) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hL : Lay c.MP' size (· ∈ curveSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have I : Inv c.MP' base size c.C.p (· ∈ curveSl.map c.sl) ([QXM, QYM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QXM, QYM, AP, BP], i ∈ curveSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · show sv c base s AP < _; rw [hap]; exact hmont _
      · show sv c base s BP < _; rw [hbp]; exact hmont _
  rw [WP.block_append_iff]
  refine WP.mono (fprog_ok hL hpR (Impl.Ecdh.X86_64.Cfg.curveOps c) I (fun op hop x hx => ?_)
    (by rw [curveOps_eq]; exact readsOk_rename c.sl curveN_reads)) fun s₃ ⟨PK, I₃⟩ => ?_
  · rw [curveOps_eq] at hop
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (curveN_slots op₀ h₀ i hi)
  have hW1 : c.sl W1 ∈ validAfter (Impl.Ecdh.X86_64.Cfg.curveOps c) ([QXM, QYM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [Impl.Ecdh.X86_64.Cfg.curveOps, FOp.out]))
  have v₃ : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl W1) c.n) = _ := I₃.val _ hW1
  have lt₃ : wordsVal s₃.mem base (c.sl W1) c.n < c.C.p := I₃.lt _ hW1
  rw [curveOps_eq, congrFun (runOps_rename c.sl curveN _ fun _ _ y h => sl_inj c h0 h) W1,
    curveN_run] at v₃
  have U₃ : Unch base (slW c [W0, W1, W2, W3, TMP]) s.mem s₃.mem := PK.unch.mono fun w hw => by
    rw [curveOps_eq, List.map_map] at hw
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨op, ⟨op₀, h₀, rfl⟩, rfl⟩ | rfl
    · exact List.mem_map.mpr ⟨op₀.out, curveN_out op₀ h₀, by rw [Function.comp_apply, FOp.out_rename]; rfl⟩
    · exact List.mem_map_of_mem (by decide)
  have hs₃ := PK.scr hs
  refine WP.mono (checkZero_ok c hs₃ h0 (sl_le c h7 (i := W1) (by decide)) hF) fun s₄ ⟨f₄, k₄, O₄⟩ => ?_
  refine ⟨hs₃.of_keepRegs k₄ (by decide), fun r hr => ?_, by rw [k₄.rd, PK.rd], by rw [k₄.wr, PK.wr],
    U₃.trans O₄.unch, ?_⟩
  · rw [k₄.gpr r (fun h => hr (by simp at h; rcases h with rfl | rfl <;> simp [clob])), PK.gpr r hr]
  · have hz : wordsVal s₃.mem base (c.sl W1) c.n = 0 ↔
        OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM)) := by
      rw [← toM_eq_zero_iff hpR lt₃, v₃]
      show _ * _ - ((_ * _ * _ + toM _ _ (sv c base s AP) * _) + toM _ _ (sv c base s BP)) = 0 ↔ _
      rw [hap, hbp, toM_cmont hc, toM_cmont hc]
    rw [f₄, flag_unch U₃ h7 h0 hn (by decide), hf, mask_and]
    simp only [mask, hz]

/-! ## The point for the ladder -/

theorem mask_bool (P : Prop) [Decidable P] : mask P = if decide P then BitVec.allOnes 64 else 0 := by
  simp only [mask, decide_eq_true_eq]

theorem select_eq (c : Cfg) : Impl.Ecdh.X86_64.Cfg.select c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)) := by
  simp only [Impl.Ecdh.X86_64.Cfg.select, List.append_assoc]

theorem select_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.select c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.rax, .rcx, .rdx] s s' ∧ Unch base (slW c [PX, PY]) s.mem s'.mem ∧
      sv c base s' PX = (if P then sv c base s QXM else sv c base s GX) ∧
      sv c base s' PY = (if P then sv c base s QYM else sv c base s GY) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    have := sl_apart c h; omega
  rw [select_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by have := sl_le c h7 (i := FLAG) (by decide); omega))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hc₁ : s₁.gpr .rcx = if decide P then BitVec.allOnes 64 else 0 := by rw [e₁, hf, mask_bool]
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok (decide P) c.n hs₁ hc₁ (sl_le c h7 (i := PX) (by decide))
    (sl_le c h7 (i := GX) (by decide)) (sl_le c h7 (i := QXM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hc₂ : s₂.gpr .rcx = if decide P then BitVec.allOnes 64 else 0 := by rw [k₂.gpr _ (by decide), hc₁]
  refine WP.mono (sel_ok (decide P) c.n hs₂ hc₂ (sl_le c h7 (i := PY) (by decide))
    (sl_le c h7 (i := GY) (by decide)) (sl_le c h7 (i := QYM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine ⟨hs₂.of_keepRegs k₃ (by decide), ((Keeps.regs k₁).mono (by sub_regs)).trans
    ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))), ?_, ?_, ?_⟩
  · have := O₂.unch.trans O₃.unch
    rw [hm₁] at this
    exact this.mono fun w hw => by simpa using hw
  · show wordsVal s₃.mem _ _ _ = _
    rw [sv_out O₃ h7 hn (by decide) (by decide), e₂, hm₁]
    by_cases hP : P <;> simp [hP]
  · show wordsVal s₃.mem _ _ _ = _
    rw [e₃, sv_out O₂ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide), hm₁]
    by_cases hP : P <;> simp [hP]

/-! ## The whole validation -/

theorem validate_wp (c : Cfg) {s : State} {Q : State → Prop} :
    WP isa (Impl.Ecdh.X86_64.Cfg.validate c) s Q ↔
      WP isa (.block ((Impl.Mont.X86_64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P) ++
        Impl.Mont.X86_64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)) ++
        ((fprog c.MP' (Impl.Ecdh.X86_64.Cfg.curveOps c) ++ Impl.Ecdh.X86_64.Cfg.checkZero c (c.sl W1)) ++
          Impl.Ecdh.X86_64.Cfg.select c))) s Q := by
  rw [Impl.Ecdh.X86_64.Cfg.validate, blocks_wp]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, fprog,
    List.flatMap_def, List.append_assoc]

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

theorem validate_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.X86_64.Cfg.validate c) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (PeerOk c base s P₀) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  rw [validate_wp, WP.block_append_iff]
  refine WP.mono (mont_ok hc hs (modP_of hc F.mp) hr2) fun s₂ Mp => ?_
  have F₂ := F.unch h7 hn (fixedOk_slW (l := [QXM, QYM, TMP]) (by decide)) Mp.unch
  have e₂ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP] → sv c base s₂ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slW hl)
  rw [WP.block_append_iff]
  refine WP.mono (curve_ok hc Mp.scr Mp.mod Mp.x_lt Mp.y_lt F₂.ap (P₀ := P₀)
    (by rw [e₂ (i := BP) (by decide) (by decide)]; exact hbp)
    (by rw [flag_unch Mp.unch h7 h0 hn (by decide)]; exact hf)) fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄⟩ => ?_
  rw [Mp.x, Mp.y] at f₄
  have F₄ := F₂.unch h7 hn ((fixedOk_slW (l := [W0, W1, W2, W3, TMP]) (by decide)).append fixedOk_flag) U₄
  refine WP.mono (select_ok hc hs₄ f₄) fun s₆ ⟨hs₆, k₆, U₆, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3, TMP] → i ≠ FLAG → sv c base s₄ i = sv c base s₂ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have F₆ := F₄.unch h7 hn (fixedOk_slW (l := [PX, PY]) (by decide)) U₆
  have qx : sv c base s₄ QXM = sv c base s₂ QXM := q₄ (by decide) (by decide) (by decide)
  have qy : sv c base s₄ QYM = sv c base s₂ QYM := q₄ (by decide) (by decide) (by decide)
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine ⟨hs₆, fun r hr => ?_, by rw [k₆.rd, rd₄, Mp.rd], by rw [k₆.wr, wr₄, Mp.wr], ?_,
    by rw [flag_unch U₆ h7 h0 hn (by decide)]; exact f₄, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr r (fun h => hr (by simp at h; rcases h with rfl | rfl | rfl <;> simp [clob])), g₄ r hr,
      Mp.gpr r hr]
  · have sub : ∀ i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY], i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, PY] := by
      decide
    have hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY]) →
        ∀ w ∈ slW c l, w ∈ slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)] := fun hl w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (sub i (hl i hi)))
    refine ((Mp.unch.trans U₄).trans U₆).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact hsl (by decide) w hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact hsl (by decide) w hw
        · exact List.mem_append_right _ hw
    · exact hsl (by decide) w hw
  · rw [px]; split
    · rw [qx]; exact Mp.x_lt
    · exact lt_of_eq_of_lt F₄.gx (hmont _)
  · rw [py]; split
    · rw [qy]; exact Mp.y_lt
    · exact lt_of_eq_of_lt F₄.gy (hmont _)
  · rw [px]; split
    · rw [qx, Mp.x]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GX) c.n) = _
      rw [F₄.gx, toM_cmont hc]
  · rw [py]; split
    · rw [qy, Mp.y]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GY) c.n) = _
      rw [F₄.gy, toM_cmont hc]

end VG.Proof.Ecdh.X86_64

/-!
## `[d]P` and `Z^(p-2)`

The signature's ladder with its point at `PX`, `PY`, `ONEP` (`ladderQ`),
whose slots are apart as `ladder_ok` needs (`ladLayQ`, as `ladLay`), then
the signature's power (`ladPow_ok`, as `stage₂`), for any invariant of the
ladder: `Main.lean` gives the one of the group law, that `R` represents
`[k >>> j]P`.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY)

variable {c : Cfg}

theorem ladLayQ (hc : CfgOk c) : LadLay (Impl.Ecdh.X86_64.Cfg.ladderQ c) size := by
  have hn := hc.n0
  have h7 := hc.n7
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, PX, PY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 31 by omega⟩, bitsAt_le c h7 (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, PX, PY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, PX, PY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c (i := TMP) (by decide) 0 0)

theorem ladWQ_eq (c : Cfg) : ladW (Impl.Ecdh.X86_64.Cfg.ladderQ c) = slW c [RX, RY, RZ, T0, T1, T2, T3,
    T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] := rfl

/-- What the ladder and the power leave: `Q 0` accepts what `R` holds. -/
structure LadPost (c : Cfg) (base : Addr) (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s s' : State) :
    Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ powClob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
    TX, TY, TZ, TMP] ++ slW c [ACC, PT, TMP]) s.mem s'.mem
  q : Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ))
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- The ladder, from `R = O`, then `Z^(p-2)`, for any invariant `Q` that an
iteration keeps and that `Q (64 n)` accepts `O`. -/
theorem ladPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 64}
    (F : Fixed c base g s.mem) {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (Impl.Ecdh.X86_64.Cfg.ladderQ c) c.C base s k Q) (hO : Q (64 * c.n) 0 1 0)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', LadPost c base Q s s' → WP isa rest s' R) :
    WP isa (.seq (ladder (Impl.Ecdh.X86_64.Cfg.ladderQ c)) (.seq (pow c.powP) rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x ∈ ladR (Impl.Ecdh.X86_64.Cfg.ladderQ c), wordsVal s.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt F.b3p (hmont _)
    · exact hpx
    · exact hpy
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt hrx (by omega)
    · exact lt_of_eq_of_lt hry (hmont _)
    · exact lt_of_eq_of_lt hrz (by omega)
  have hR : Q (64 * c.n) (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) := by
    show Q _ (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ))
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero]
    exact hO
  refine WP.seq (WP.mono (ladder_ok (L := Impl.Ecdh.X86_64.Cfg.ladderQ c) (k := k) (ladLayQ hc)
    hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  rw [ladWQ_eq] at U₅
  have hs₅ := hs.of_keepRegs K₅ (rdi_not_powClob _)
  have F₅ := F.unch h7 hn (fixedOk_slW (by decide)) U₅
  have rz₅ : wordsVal s₅.mem base (c.sl RZ) c.n < c.C.p :=
    L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) hpR hs₅ M₅ rz₅ F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 hn (j := 1) (by decide) ht (tbl_apart_slW (by decide) 1 t)]
      exact ht₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWP_eq] at U₆
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_slW h₁)
  refine ⟨hs₅.of_keepRegs K₆ (rdi_not_powClob _), fun r hr => by rw [K₆.gpr r hr, K₅.gpr r hr],
    by rw [K₆.rd, K₅.rd], by rw [K₆.wr, K₅.wr], U₅.trans U₆, ?_, lt₆, ?_, ?_⟩
  · show Q 0 (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ))
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]; exact rz₅

end VG.Proof.Ecdh.X86_64
