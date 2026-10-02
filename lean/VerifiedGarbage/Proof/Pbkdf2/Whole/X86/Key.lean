import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the prologue and the key

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers in `scratch` (`save_ok`, which is
`VG.Proof.Hmac.Generic.X86.save_ok` for any amount of working space before
the save area); then the key is the password, or its digest if it is longer
than a block (`key_ok`): either gives the same `K₀` (`KeyAt`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Hmac.Generic.X86 (HashOK SavedRegs saveR InitArgs UpdArgs FinArgs init_frame upd_frame fin_frame
  saveList_ok saveMem_frameR saveMem_read saved_mem saved_pairwise zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_cmpi wp_test wp_addi wp_bswap wp_store)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey)

variable {F : Fns}

/-- Saving the registers, with `scratch` in `eax`: `VG.Proof.Hmac.Generic.X86.save_ok`, for any `H.W`. -/
theorem save_ok (H : Hash) {s : State} {sc : BitVec 32} {L : Nat} (hax : s.gpr .eax = sc)
    (hsc : ⟨sc.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : sc.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [saveR H sc] s.mem s'.mem → SavedRegs H sc s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [Hmac.Generic.X86.save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [hax]
    exact ⟨by omega, ⟨_, hsc, contains_offset (by omega) (by omega)⟩⟩
  · rw [m, hax]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## The prologue -/

theorem prologue_ok : WP isa (.block F.prologue) s₀ (KR F s₀) := by
  have hL := end_le hz; have := layout (F := F)
  have hsc := sc_mem hp
  simp only [Fns.prologue, List.cons_append]
  refine wp_movm (a := argAddr s₀ 7) (argW rfl 7) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok F.L (sc := scr s₀) (L := F.L8) u₁.gpr (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 16 ≤ F.L8; omega) hp.nsc fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine wp_mov fun s₃ u₃ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_⟩
  · rw [u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [Hmac.Generic.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)
  · rw [u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀ F, by simp, sv_sub hz⟩

/-! ## The stack and `scratch`, while `KR` holds -/

omit hz in
theorem stk48_sub {s : State} (hk : KR F s₀ s) : Region.Sub (Hmac.Generic.X86.stk s) (stkR s₀) := by
  rw [Hmac.Generic.X86.stk, hk.esp]; exact below_sub (by decide) hp.sp76

omit hz in
/-- A region of `scratch` is apart from the stack below `esp`. -/
theorem b76 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) :
    (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b48 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) :
    (Hmac.Generic.X86.stk s).Disjoint R :=
  (hp.b_s.sub_left (stk48_sub hp hk)).sub_right hR

omit hz in
/-- A part of `scratch`, as `Covers.of_sub` takes it. -/
theorem cov_part {s : State} (hk : KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_pw {s : State} (hk : KR F s₀ s) : Covers [pwR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

omit hz in
theorem cov_salt {s : State} (hk : KR F s₀ s) : Covers [saltR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a password longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `edi ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86.scr .edi F.stWO)) s fun t =>
      KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86.scr .edi F.stWO)]
  exact scr_ok hk fun s₁ u₁ => WP.block_nil ⟨hk.upd (by decide) u₁, u₁.gpr, u₁.mem⟩

omit hH in
theorem hk2_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    InitArgs (H := F.H) s .edi (dO s₀ F.stWO) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine ⟨hdi, by decide, by rw [hk.esp]; have := hp.sp76; omega, ?_, ?_, ?_⟩
  · rw [ea]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk (by omega)
  · rw [ea]; exact b48 hp hk (part_sub (by omega))
  · rw [dO_toNat hp (by omega)]; have := hp.nsc; omega

theorem hk2_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (F.H.callInit .edi) s fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine init_frame hH (hk2_args hp hz hk hdi) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, by rw [← ea]; exact r, a.cs _ (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩

omit hz hH in
/-- `update`'s arguments: the password. -/
theorem hk3_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (Fns.argM 1), .mov .edx (Fns.argM 0)]) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .esi = 0 ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 1 ∧ t.gpr .edx = pw s₀ ∧ t.mem = s.mem := by
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_arg hp k₂ (by decide) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨k₃.upd (by decide) u₄, ?_, ?_, ?_, ?_, u₄.gpr, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr]

theorem hk4_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = pw s₀) :
    UpdArgs hH s .esi .edi (dO s₀ F.stWO) (pw s₀) (scr s₀) 0 (pwl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 1).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cd := cov_pw hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (by omega))
      b_d := hp.b_pw.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.npw
      nsc := by have := hp.nsc; omega }

theorem hk4_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = pw s₀)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) ∧
        t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine upd_frame hH (hk4_args hp hz hH hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, a.cs _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r [] (by rw [ea]; exact hr) rfl
    rwa [List.nil_append, ea, hk.pwBytes hp] at this

omit hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block (([.mov .eax (Fns.argM 1), .mov .ecx (.imm 0)] : List Instr) ++
      VG.Impl.Hmac.Generic.X86.scr .edx F.hkO)) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .eax = arg s₀ 1 ∧ t.gpr .ecx = 0 ∧
        t.gpr .edx = dO s₀ F.hkO ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86.scr .edx F.hkO)]
  refine scr_ok k₂ fun s₃ u₃ => WP.block_nil ⟨k₂.upd (by decide) u₃, ?_, ?_, ?_, u₃.gpr, by
    rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem hk6_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO) :
    FinArgs hH s .edi (dO s₀ F.stWO) (dO s₀ F.hkO) (scr s₀) (arg s₀ 1) 0 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  exact
    { hst := hdi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact b48 hp hk (part_sub (by omega))
      b_o := by rw [eh]; exact b48 hp hk (part_sub (by omega))
      b_sc := b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

theorem hk6_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5)) s
      fun t => KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  refine fin_frame hH (hk6_args hp hz hH hk hdi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [eh], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (arg s₀ 1).isLt (by decide))
      (by rw [bytesAt_length, ← zero_append_ofNat (arg s₀ 1).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp hz hH in
theorem hk7_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86.scr .edx F.hkO ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ⟨(hk.upd (by decide) u₁).upd (by decide) u₂,
    by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.hashKey s fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.hashKey
  refine WP.seq (WP.mono (hk1_ok hk) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  have d₂ : s₂.gpr .edi = dO s₀ F.stWO := e₂.trans d₁
  refine WP.seq (WP.mono (hk3_ok hp k₂ d₂) fun s₃ ⟨k₃, d₃, i₃, a₃, c₃, x₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ d₃ i₃ a₃ c₃ x₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, r₄, e₄⟩ => ?_)
  have d₄ : s₄.gpr .edi = dO s₀ F.stWO := e₄.trans d₃
  refine WP.seq (WP.mono (hk5_ok hp k₄ d₄) fun s₅ ⟨k₅, d₅, a₅, c₅, x₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ d₅ a₅ c₅ x₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

/-! ## The key -/

omit hH in
theorem cmp_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => KR F s₀ t ∧ t.gpr .ecx = arg s₀ 1 ∧
      t.cf = some (decide (pwl s₀ < F.H.B + 1)) ∧ t.mem = s.mem := by
  have := hz.B
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
  refine ⟨(hk.upd (by decide) u₁).same f₂.rd f₂.wr (fun r _ => by rw [f₂.gpr]) f₂.mem, by rw [f₂.gpr, u₁.gpr], ?_,
    by rw [f₂.mem, u₁.mem]⟩
  rw [c₂, u₁.gpr, toNat_ofNat32 (by omega)]

omit hp hz in
theorem hash_len {k : List Byte} {m : Mem} {p : Addr} (h : bytesAt m p F.H.D = hH.SH.H.hash k) :
    (hH.SH.H.hash k).length = F.H.D := by
  rw [← h, bytesAt_length]

omit hp in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : F.H.B < k.length) (hl : (hH.SH.H.hash k).length = F.H.D) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB; have := hz.DB
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ F.H.B < F.H.D by omega))]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if pwl s₀ < F.H.B + 1 then pw s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if pwl s₀ < F.H.B + 1 then pwl s₀ else F.H.D

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.key s fun t => KR F s₀ t ∧ t.gpr .edx = kp F s₀ ∧ t.gpr .ecx = BitVec.ofNat 32 (kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem ((kp F s₀).setWidth 64) (kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (cmp_ok hp hz hk) fun s₁ ⟨k₁, c₁, f₁, _⟩ => ?_)
  refine WP.ite (decide (F.H.B + 1 ≤ pwl s₀)) (by
    show (s₁.cf.map (!·)) = _
    rw [f₁]; simp only [Option.map_some, ← decide_not, Nat.not_lt])
    (fun hT => ?_) fun hF => ?_
  · have hlt : ¬ pwl s₀ < F.H.B + 1 := by have := of_decide_eq_true hT; omega
    simp only [kp, kl, hlt, ↓reduceIte]
    refine WP.mono (hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D
    rw [show (dO s₀ F.hkO).setWidth 64 = A s₀ F.hkO from dO_addr hp (by have := end_le hz; have := layout (F := F); omega),
      b, blockKey_hash hz hH (by rw [bytesAt_length]; omega) (hash_len hH b)]
  · have hlt : pwl s₀ < F.H.B + 1 := by have := of_decide_eq_false hF; omega
    simp only [kp, kl, hlt, ↓reduceIte]
    refine wp_arg hp k₁ (by decide) fun s₂ u₂ => WP.block_nil ⟨k₁.upd (by decide) u₂, u₂.gpr, ?_, ?_⟩
    · rw [u₂.other _ (by decide), c₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [u₂.mem, k₁.pwBytes hp]

end

/-! ## Where the key is -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- The key's region is the password, or the hashed password in `scratch`. -/
theorem key_cases : (kp F s₀ = pw s₀ ∧ kl F s₀ = pwl s₀ ∧ pwl s₀ ≤ F.H.B) ∨
    ((kp F s₀).setWidth 64 = A s₀ F.hkO ∧ kl F s₀ = F.H.D) := by
  by_cases h : pwl s₀ < F.H.B + 1
  · exact .inl ⟨by simp [kp, h], by simp [kl, h], by omega⟩
  · refine .inr ⟨?_, by simp [kl, h]⟩
    simp only [kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega)

theorem kl_le : kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega

theorem key_toNat : (kp F s₀).toNat + kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : pwl s₀ < F.H.B + 1
  · simp only [kp, kl, h, ↓reduceIte]; exact hp.npw
  · simp only [kp, kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (by omega)]
    have := hp.nsc; omega

/-- The key is apart from the parts of `scratch` after the hashed password,
from the working space, and from the stack below `esp`. -/
theorem key_disj {R : Region} (hR : Region.Sub R (scR s₀ F))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ R := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.pw_s.sub_right hR
  · rw [h, h']; exact hd.symm

theorem key_stk {s : State} (hk : KR F s₀ s) : (stk s).Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ := by
  rw [hk.stkE]
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_pw
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (by have := end_le hz; have := layout (F := F); have := hz.D; omega))

theorem key_cov {s : State} (hk : KR F s₀ s) : Covers [⟨(kp F s₀).setWidth 64, kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact cov_pw hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.hkO) (n := F.H.D)
        (by have := end_le hz; have := layout (F := F); have := hz.D; omega)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

end VG.Proof.Pbkdf2.Whole.X86
