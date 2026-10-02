import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.CmacTripleDes.X86.Keys

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[100, 124)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_add wp_subi wp_sub wp_andi
  wp_or wp_cmpi wp_shr wp_bswap)
open VG.X86.Straight (wordAddr)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, r`. -/
theorem wp_xorr {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  Wp.wp_xor fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

end

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := arg s₀ 0
abbrev Kl : Nat := (arg s₀ 1).toNat
abbrev O : BitVec 32 := arg s₀ 2
abbrev Sc : BitVec 32 := arg s₀ 3

abbrev ikeyR : Region := ⟨(K s₀).setWidth 64, Kl s₀⟩
abbrev outR : Region := ⟨(O s₀).setWidth 64, 400⟩
abbrev iscrR : Region := ⟨(Sc s₀).setWidth 64, 640⟩
abbrev iargsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem ((K s₀).setWidth 64) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨(Sc s₀).setWidth 64, 84⟩, ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikeyR s₀, iargsR s₀]
  wr : s₀.wr = [outR s₀, iscrR s₀]
  key_out : (ikeyR s₀).Disjoint (outR s₀)
  key_scr : (ikeyR s₀).Disjoint (iscrR s₀)
  out_scr : (outR s₀).Disjoint (iscrR s₀)
  args_out : (iargsR s₀).Disjoint (outR s₀)
  args_scr : (iargsR s₀).Disjoint (iscrR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (iscrR s₀)
  key_fit : (K s₀).toNat + Kl s₀ ≤ 2 ^ 32
  out_fit : (O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = Sc s₀
  esi : s.gpr .esi = Sc s₀ + BitVec.ofNat 32 (100 + 8 * i)
  edi : s.gpr .edi = O s₀ + BitVec.ofNat 32 (128 * i)
  edx : s.gpr .edx = BitVec.ofNat 32 (3 - i)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 (100 + 8 * j)) 32 ++
    s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 (104 + 8 * j)) 32 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW ((O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, ⟨(O s₀).setWidth 64, 384⟩]
    (savedMem s₀ (Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions s₀.wr ((O s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((K s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega))

theorem IPre.scrEa {s : State} (h : s.gpr .ebp = Sc s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (Sc s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

theorem IPre.keyEa {s : State} (h : s.gpr .ecx = K s₀) {d : Nat} (hd : d < Kl s₀) :
    s.ea (at_ .ecx d) = (K s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.key_fit; omega)

theorem IPre.argAddr_eq {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

theorem IPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact in_rw (r := iargsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

/-- The arguments, unchanged outside the output and the scratch buffer. -/
theorem IPre.arg_eq {m : Mem} (hf : Frame [outR s₀, iscrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (iargsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  refine hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.args_out.sub_left hsub
  · exact hp.args_scr.sub_left hsub

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ Kl s₀) :
    m.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(K s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 32) ++
      bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j + 4)) 32) = kw s₀ j := by
  rw [bswap_eq, bswap_eq, byteRev32_append, kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ Kl s₀) (ho : o + 4 ≤ 640)
    (hcx : s.gpr .ecx = K s₀) (hbp : s.gpr .ebp = Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 o)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.mov .eax (.mem (at_ .ecx d)) :: .bswap .eax :: .store (at_ .ebp o) .eax :: rest)) s Q
  refine wp_movm (hp.keyEa hcx (by omega)) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (hp.scrEa (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbp]) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[100, 124)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 100 ≤ d) (h₂ : d + 4 ≤ 124) :
    (⟨S + BitVec.ofNat 64 100, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 100 + BitVec.ofNat 64 (d - 100) from
    (Offset.add_add_eq _ (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (arg s₀ 3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  have kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega
  rw [show initPre = .seq (.block (.mov .eax (stk 16) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
      (.mov .ebp (.reg .eax) :: .mov .ecx (stk 4) :: (keyWord 0 100 ++ (keyWord 4 104 ++ (keyWord 8 108 ++
        (keyWord 12 112 ++ ([.mov .eax (stk 8), .alu .cmp .eax (.imm 16)] : List Instr)))))))))
      (.seq (.ite .e (.block [.mov .eax (.mem (at_ .ecx 0)), .mov .edx (.mem (at_ .ecx 4))])
          (.block [.mov .eax (.mem (at_ .ecx 16)), .mov .edx (.mem (at_ .ecx 20))]))
        (.block [.bswap .eax, .bswap .edx, .store (at_ .ebp 116) .eax, .store (at_ .ebp 120) .edx,
          .mov .esi (.reg .ebp), .alu .add .esi (.imm 100), .mov .edi (stk 12), .mov .edx (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine wp_arg (s₀ := s₀) 3 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.wr]
    exact ⟨by omega, hp.inScr (by omega) (by decide)⟩
  have hm₂ : s₂.mem = savedMem s₀ (Sc s₀) := by
    rw [m₂, u₁.mem, u₁.gpr, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have sv : Frame [iscrR s₀] s₀.mem (savedMem s₀ (Sc s₀)) := (savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have toOS : ∀ {m}, Frame [iscrR s₀] s₀.mem m → Frame [outR s₀, iscrR s₀] s₀.mem m := fun hf =>
    hf.mono (by simp)
  have scrC : ∀ d, d + 4 ≤ 640 → (iscrR s₀).Contains ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  refine wp_mov fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .ebp = Sc s₀ := by rw [u₃.gpr, g₂, u₁.gpr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr]
  refine wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_eq (toOS sv) (by decide)) fun s₄ u₄ => ?_
  have cx₄ : s₄.gpr .ecx = K s₀ := u₄.gpr
  have bp₄ : s₄.gpr .ebp = Sc s₀ := by rw [u₄.other _ (by decide), e₃]
  -- The four words of the first two DES keys.
  refine keyWord_wp hp (by omega) (by decide) cx₄ bp₄ (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃])
    (by rw [u₄.mem, u₃.mem, hm₂]; exact sv) fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  have F₅ : Frame [iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅, u₄.mem, u₃.mem, hm₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by rw [g₅ _ (by decide), cx₄]) (by rw [g₅ _ (by decide), bp₄])
    (by rw [rd₅, u₄.rd, rd₃]) (by rw [wr₅, u₄.wr, wr₃]) F₅ fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  have F₆ : Frame [iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 104 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by rw [g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₆, wr₅, u₄.wr, wr₃]) F₆ fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  have F₇ : Frame [iscrR s₀] s₀.mem s₇.mem := by
    rw [m₇]; exact F₆.writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₇, rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₇, wr₆, wr₅, u₄.wr, wr₃]) F₇ fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  have F₈ : Frame [iscrR s₀] s₀.mem s₈.mem := by
    rw [m₈]; exact F₇.writeW (List.mem_singleton_self _) _ (scrC 112 (by decide))
  have g₈' : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r h => by rw [g₈ r h, g₇ r h, g₆ r h, g₅ r h]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, rd₇, rd₆, rd₅, u₄.rd, rd₃]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, wr₅, u₄.wr, wr₃]
  have esp₈ : s₈.gpr .esp = s₀.gpr .esp := by rw [g₈' _ (by decide), u₄.other _ (by decide), esp₃]
  refine wp_arg (s₀ := s₀) 1 rfl esp₈ (hp.argIn rd₈' wr₈' (by decide)) (hp.arg_eq (toOS F₈) (by decide))
    fun s₉ u₉ => wp_cmpi fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have ev : isa.eval .e s₁₀ = some (decide (Kl s₀ = 16)) := by
    rw [eval_e', z₁₀, u₉.gpr, show arg s₀ 1 = BitVec.ofNat 32 (Kl s₀) by simp [Kl],
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, MdStream.X86.sub_beq (arg s₀ 1).isLt (by decide)]
  have g₁₀ : ∀ r, r ≠ .eax → s₁₀.gpr r = s₄.gpr r := fun r h => by rw [f₁₀.gpr, u₉.other _ h, g₈' r h]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [f₁₀.rd, u₉.rd, rd₈']
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [f₁₀.wr, u₉.wr, wr₈']
  have mem₁₀ : s₁₀.mem = s₈.mem := by rw [f₁₀.mem, u₉.mem]
  -- The third DES key.
  have third : ∀ d, d + 8 ≤ Kl s₀ →
      WP isa (.block [.mov .eax (.mem (at_ .ecx d)), .mov .edx (.mem (at_ .ecx (d + 4)))]) s₁₀ fun s₁₁ =>
        s₁₁.gpr .eax = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 ∧
        s₁₁.gpr .edx = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
        s₁₁.wr = s₀.wr := by
    intro d hd
    have cx : s₁₀.gpr .ecx = K s₀ := by rw [g₁₀ _ (by decide), cx₄]
    refine wp_movm (hp.keyEa cx (by omega)) (by rw [rd₁₀, wr₁₀]; exact hp.inKey (by omega) (by decide))
      fun s₁₁ u₁₁ => ?_
    refine wp_movm (hp.keyEa (by rw [u₁₁.other _ (by decide), cx]) (by omega))
      (by rw [u₁₁.rd, u₁₁.wr, rd₁₀, wr₁₀]; exact hp.inKey (by omega) (by decide))
      fun s₁₂ u₁₂ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr, mem₁₀, hp.keyRead F₈ (by omega)]
    · rw [u₁₂.gpr, u₁₁.mem, mem₁₀, hp.keyRead F₈ (by omega)]
    · rw [u₁₂.other _ h5, u₁₁.other _ h4]
    · rw [u₁₂.mem, u₁₁.mem, mem₁₀]
    · rw [u₁₂.rd, u₁₁.rd, rd₁₀]
    · rw [u₁₂.wr, u₁₁.wr, wr₁₀]
  refine WP.seq (WP.mono (Q := fun (s₁₁ : State) =>
      s₁₁.gpr .eax = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32 ∧
      s₁₁.gpr .edx = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
      s₁₁.wr = s₀.wr) ?_ fun s₁₁ h₁₁ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega)
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega)
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₁₁, dx₁₁, g₁₁, m₁₁, rd₁₁, wr₁₁⟩ := h₁₁
  have bp₁₁ : s₁₁.gpr .ebp = Sc s₀ := by rw [g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), bp₄]
  refine wp_bswap fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  have bp₁₃ : s₁₃.gpr .ebp = Sc s₀ := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), bp₁₁]
  refine wp_store (hp.scrEa bp₁₃ (by decide)) (by rw [u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide))
    fun s₁₄ w₁₄ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₄.gpr, bp₁₃]) (by decide))
    (by rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide)) fun s₁₅ w₁₅ => ?_
  refine wp_mov fun s₁₆ u₁₆ => wp_addi fun s₁₇ u₁₇ => ?_
  have esp₁₇ : s₁₇.gpr .esp = s₀.gpr .esp := by
    rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), w₁₅.gpr, w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), u₄.other _ (by decide), esp₃]
  have rd₁₇ : s₁₇.rd = s₀.rd := by rw [u₁₇.rd, u₁₆.rd, w₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁]
  have wr₁₇ : s₁₇.wr = s₀.wr := by rw [u₁₇.wr, u₁₆.wr, w₁₅.wr, w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]
  have mem₁₅ : s₁₅.mem = ((((((savedMem s₀ (Sc s₀)).writeW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 100)
      (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 0) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 104) (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 4) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 108) (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 8) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 112)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 12) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 116)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 120)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32)) := by
    rw [w₁₅.mem, w₁₄.mem, w₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₃.mem, u₁₂.mem,
      u₁₂.other .edx (by decide), ax₁₁, dx₁₁, m₁₁, m₈, m₇, m₆, m₅, u₄.mem, u₃.mem, hm₂]
  refine wp_arg (s₀ := s₀) 2 rfl esp₁₇ (hp.argIn rd₁₇ wr₁₇ (by decide))
    (by
      rw [u₁₇.mem, u₁₆.mem, mem₁₅]
      refine hp.arg_eq (toOS ?_) (by decide)
      exact (((((sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 104 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))).writeW
        (List.mem_singleton_self _) _ (scrC 112 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 116 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 120 (by decide)))
    fun s₁₈ u₁₈ => wp_movi fun s₁₉ u₁₉ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.other _ (by decide),
      w₁₅.gpr, w₁₄.gpr, bp₁₃]
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, w₁₅.gpr, w₁₄.gpr, bp₁₃]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.gpr, add_zero32]
  · rw [u₁₉.gpr]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), esp₁₇]
  · rw [u₁₉.rd, u₁₈.rd, rd₁₇]
  · rw [u₁₉.wr, u₁₈.wr, wr₁₇]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅, ← kw_eq (s₀ := s₀) j]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅]
    have c : ∀ d, 100 ≤ d → d + 4 ≤ 124 → (⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩ : Region).Contains
        ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 100 (by decide) (by decide))).writeW (by simp) _
      (c 104 (by decide) (by decide))).writeW (by simp) _ (c 108 (by decide) (by decide))).writeW (by simp) _
      (c 112 (by decide) (by decide))).writeW (by simp) _ (c 116 (by decide) (by decide))).writeW (by simp) _
      (c 120 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => KInv s₀ (i + 1) s' ∧ s'.zf = some (decide (3 - (i + 1) = 0)) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  have oN : (O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hok : Straight.Ok kCfg s := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
    · simp only [kCfg] at hk
      rw [show kCfg.base = .edi from rfl, h.edi, h.wr, hp.wr]
      exact in_rw (r := outR s₀) (by simp) (contains_w_off (by omega) (by omega))
    · simp only [kCfg] at hk
      rw [show kCfg.ext = .esi from rfl, h.esi, h.rd, h.wr, hp.rd, hp.wr]
      exact in_rw (r := iscrR s₀) (by simp) (contains_w_off (by omega) (by omega))
    · show (s.gpr .edi).toNat + 4 * 32 ≤ 2 ^ 32
      rw [h.edi, oN]; omega
    · simp only [kCfg] at hk hj
      rw [show kCfg.base = .edi from rfl, show kCfg.ext = .esi from rfl, h.edi, h.esi]
      exact hp.out_scr.sep (contains_w_off (by omega) (by omega)) (contains_w_off (by omega) (by omega))
  obtain ⟨s₁, run₁, rk₁, hi₁, rd₁, wr₁, k₁, f₁⟩ := roundKeys_ok hok
  rw [keysBody, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine wp_addi fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  have kk : ∀ r ∈ kKept, s₁.gpr r = s.gpr r := k₁
  have dk : desKey s = kw s₀ i := by
    rw [desKey, h.esi, wordAddr_off _ (by omega), wordAddr_off _ (by omega), show 100 + 8 * i + 4 * 0 = 100 + 8 * i by omega,
      show 100 + 8 * i + 4 * 1 = 104 + 8 * i by omega, h.keys i hi]
  have slotR : Straight.slotRegion kCfg s = ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [Straight.slotRegion]; rw [show kCfg.base = .edi from rfl, h.edi, ← addr_zero, addr_off2 (by omega), add0]; rfl
  rw [slotR] at f₁
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have dx₁ : s₁.gpr .edx = BitVec.ofNat 32 (3 - i) := by rw [kk _ (by simp [kKept]), h.edx]
  have dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := by
    rw [ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  have wA : ∀ k < 32, wordAddr (s.gpr .edi) k = (O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by rw [h.edi, wordAddr_off _ (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [kKept]), h.ebp]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), kk _ (by simp [kKept]), h.esi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 100 + 8 * i + 8 = 100 + 8 * (i + 1) by omega]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, kk _ (by simp [kKept]), h.edi,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, dec]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [kKept]), h.esp]
  · rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [m₄, ← h.keys j hj]
    have keep : ∀ d, 100 ≤ d → d + 4 ≤ 124 → s₁.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
        s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ =>
      f₁.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)))
        (by decide)
    rw [keep _ (by omega) (by omega), keep _ (by omega) (by omega)]
  · rw [m₄]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₁.readW (r := ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega,
        ← wA (2 * j + 1) (by omega), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega, ← wA (2 * j) (by omega),
        append_of_hi _ _ (hi₁ j hj), rk₁ j hj, dk, kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₄]
    exact h.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(O s₀).setWidth 64, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)
  · rw [z₄, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.X86.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [eval_ne', z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne', z']; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `eax:edx` and stores it, as bytes, at `[edi + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop}
    (ha : addr (s.gpr .edi) d = a) (ha4 : addr (s.gpr .edi) (d + 4) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .eax ++ s'.gpr .edx = dbl64 (s.gpr .eax ++ s.gpr .edx) →
      s'.mem = (s.mem.writeW a (bswap (s'.gpr .eax))).writeW (a + BitVec.ofNat 64 4) (bswap (s'.gpr .edx)) →
      (∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .ecx (.reg .eax) :: .shift .shr .ecx 31 :: .mov .ebx (.imm 0) ::
    .alu .sub .ebx (.reg .ecx) :: .alu .and .ebx (.imm 0x1b) :: .mov .ecx (.reg .edx) :: .shift .shr .ecx 31 ::
    .alu .add .eax (.reg .eax) :: .alu .or .eax (.reg .ecx) :: .alu .add .edx (.reg .edx) ::
    .alu .xor .edx (.reg .ebx) :: .mov .ecx (.reg .eax) :: .bswap .ecx :: .store (at_ .edi d) .ecx ::
    .mov .ecx (.reg .edx) :: .bswap .ecx :: .store (at_ .edi (d + 4)) .ecx :: rest)) s Q
  refine wp_mov fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ _ =>
    wp_andi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_shr (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_or fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => wp_xorr fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  have g₁₃ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s₁₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.other _ hr.2.2.1, u₁₂.other _ hr.2.2.1, u₁₁.other _ hr.2.2.2, u₁₀.other _ hr.2.2.2, u₉.other _ hr.1,
      u₈.other _ hr.1, u₇.other _ hr.2.2.1, u₆.other _ hr.2.2.1, u₅.other _ hr.2.1, u₄.other _ hr.2.1,
      u₃.other _ hr.2.1, u₂.other _ hr.2.2.1, u₁.other _ hr.2.2.1]
  have m₁₃ : s₁₃.mem = s.mem := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₁₃ : s₁₃.wr = s.wr := by
    rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have di₁₃ : s₁₃.gpr .edi = s.gpr .edi := g₁₃ _ (by decide)
  refine wp_store (by rw [ea_at', di₁₃, ha]) (by rw [wr₁₃]; exact w0) fun s₁₄ w₁₄ => ?_
  refine wp_mov fun s₁₅ u₁₅ => wp_bswap fun s₁₆ u₁₆ => ?_
  refine wp_store (by rw [ea_at', u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, di₁₃, ha4])
    (by rw [u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]; exact w4) fun s₁₇ w₁₇ => ?_
  have r0f : s₁₇.gpr .eax = s₁₁.gpr .eax := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  have r1f : s₁₇.gpr .edx = s₁₁.gpr .edx := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  refine k s₁₇ ?_ ?_ (fun r hr => ?_) ?_ ?_
  · have a3 : s₁₀.gpr .ebx = ((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr]
    have a0 : s₁₁.gpr .eax = s.gpr .eax <<< 1 ||| s.gpr .edx >>> 31 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr,
        u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), add_self]
    have a1 : s₁₁.gpr .edx =
        s.gpr .edx <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₁₁.gpr, a3, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), add_self]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₇.mem, u₁₆.mem, u₁₅.mem, w₁₄.mem, m₁₃, u₁₆.gpr, u₁₅.gpr, w₁₄.gpr, u₁₃.other .edx (by decide),
      u₁₃.gpr, u₁₂.gpr, r0f, r1f, u₁₂.other .edx (by decide)]
  · rw [w₁₇.gpr, u₁₆.other _ (by simp_all), u₁₅.other _ (by simp_all), w₁₄.gpr, g₁₃ r hr]
  · rw [w₁₇.rd, u₁₆.rd, u₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd,
      u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  have of' : (arg s₀ 2).toNat + 400 ≤ 2 ^ 32 := hp.out_fit
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  have F₂ : Frame [outR s₀, iscrR s₀] s₀.mem s₂.mem :=
    ((savedMem_frame s₀ (Sc s₀)).sub fun r hr => ⟨iscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩)
  -- The key schedule is in place.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem ((O s₀).setWidth 64) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  refine WP.seq ?_
  simp only [stk]
  refine wp_arg (s₀ := s₀) 2 rfl h₂.esp (hp.argIn h₂.rd h₂.wr (by decide)) (hp.arg_eq F₂ (by decide))
    fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  have g₅ : ∀ r, r ∉ [Reg.eax, .edx, .esi] → s₅.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.1, u₄.other _ hr.1, u₃.other _ hr.2.2]
  have esi₅ : s₅.gpr .esi = O s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have ebp₅ : s₅.gpr .ebp = Sc s₀ := by rw [g₅ _ (by decide), h₂.ebp]
  have ax₅ : s₅.gpr .eax ++ s₅.gpr .edx = (0 : BitVec 64) := by rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr]; rfl
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, h₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]
  have hsch₅ : sch s₅ = Spec.TripleDes.expandKey (keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₅.mem ((s₅.gpr .esi).setWidth 64) = _
    rw [esi₅, m₅, hsch₂]
  have bp : BlockPre s₅ :=
    { sched := ⟨400, by rw [esi₅, rd₅, wr₅, hp.rd, hp.wr]; simp, by decide, by rw [esi₅]; exact of⟩
      scr := ⟨640, by rw [ebp₅, wr₅, hp.wr]; simp, by decide, by rw [ebp₅]; exact sf⟩
      disj := by
        rw [esi₅, ebp₅]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₆ ⟨same₆, esi₆, ax₆⟩ => ?_)
  rw [ax₅, hsch₅] at ax₆
  have xR₅ : xR s₅ = ⟨(Sc s₀).setWidth 64, 84⟩ := by rw [xR, ebp₅]
  have f₆ : Frame [⟨(Sc s₀).setWidth 64, 84⟩] s₂.mem s₆.mem := by rw [← m₅, ← xR₅]; exact same₆.frame
  have F₆ : Frame [outR s₀, iscrR s₀] s₀.mem s₆.mem :=
    F₂.trans (f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [same₆.esp, g₅ _ (by decide), h₂.esp]
  have ebp₆ : s₆.gpr .ebp = Sc s₀ := by rw [same₆.ebp, ebp₅]
  have rd₆ : s₆.rd = s₀.rd := by rw [same₆.rd, rd₅]
  have wr₆ : s₆.wr = s₀.wr := by rw [same₆.wr, wr₅]
  show WP isa (.block (.mov .edi (stk 12) :: .alu .add .edi (.imm 384) :: (dbl 0 ++ (dbl 8 ++ restore)))) s₆ _
  refine wp_arg (s₀ := s₀) 2 rfl esp₆ (hp.argIn rd₆ wr₆ (by decide)) (hp.arg_eq F₆ (by decide))
    fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  have di₈ : s₈.gpr .edi = O s₀ + 384 := by rw [u₈.gpr, u₇.gpr]
  have oA : ∀ d, d < 16 → addr (s₈.gpr .edi) d = (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [di₈, show (384 : BitVec 32) = BitVec.ofNat 32 384 from rfl, addr_off2 (by omega), Offset.add_add]
  have wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, u₇.wr, wr₆]; exact hp.inOut (by omega) (by decide)
  have a4 : ∀ d, (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine dbl_wp (a := (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 0)) (oA 0 (by decide))
    (by rw [oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ => ?_
  refine dbl_wp (a := (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 8)) (by rw [g₉ _ (by decide), oA 8 (by decide)])
    (by rw [g₉ _ (by decide), oA 12 (by decide), a4]) (by rw [wr₉]; exact wO 8 (by decide))
    (by rw [wr₉, a4]; exact wO 12 (by decide)) fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ => ?_
  have ebp₁₀ : s₁₀.gpr .ebp = Sc s₀ := by
    rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [ikeyR s₀, iargsR s₀, outR s₀, iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, u₇.rd, u₇.wr, rd₆, wr₆, hp.rd, hp.wr]; rfl
  -- What changed since the registers were saved.
  have oC : ∀ d, d + 4 ≤ 16 → (outR s₀).Contains ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega) (by omega)
  have F₁₀ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₁₀.mem := by
    have F₂' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩
    have F₆' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₆.mem := F₂'.trans (f₆.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
    exact (((F₆'.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (restore_ok ebp₁₀ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, ho, m', _, _⟩ => ⟨restored (S := Sc s₀) (fun d h₁' h₂' => ?_) hl ?_ ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm
  · rw [ho _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), esp₆]
  · rw [m', F₁₀.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (savedMem_frame s₀ (Sc s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_out
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem ((O s₀).setWidth 64) = Spec.TripleDes.expandKey (keyB s₀)
    rw [m', ← hsch₂]
    refine scheduleAt_frame (rs := [iscrR s₀, ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨(O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
      exact ((((f₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem ((O s₀).setWidth 64 + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    rw [subkeys_tdes, m', bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem,
      u₇.mem]
    simp (disch := decide) only [Offset.add_add, readW_writeW_far, Mem.readW_writeW_self32]
    rw [bswap_eq, bswap_eq, bswap_eq, bswap_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .eax (by decide), u₈.other .edx (by decide), u₇.other .eax (by decide), u₇.other .edx (by decide), ax₆]

end VG.Proof.CmacTripleDes.X86
