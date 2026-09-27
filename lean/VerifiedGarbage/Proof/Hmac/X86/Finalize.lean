import VerifiedGarbage.Proof.Hmac.X86.Common
import VerifiedGarbage.Spec.Hmac.X86

/-!
# HMAC-SHA-256 on x86 (32-bit): `finalize`

Untrusted: everything here is checked by Lean. The inner hash is the code of
`vg_sha256_finalize` up to writing the digest (`finalizeHash`), run on our
state with its permissions narrowed to those of `vg_sha256_finalize` and
reasoned about with that function's own proof (`WP.narrow`); the outer hash
is one inlined compression of a block laid out at known offsets.
-/

namespace VG.Proof.Hmac.X86.Finalize

open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append repr_congr compressList_append
  hash_one lenBytes rest)
open VG.Proof.Hmac.X86
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes countX86 Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256 countFinalizeX86)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev ou : BitVec 32 := arg s₀ 1
abbrev out : BitVec 32 := arg s₀ 4
abbrev scr : BitVec 32 := arg s₀ 5
abbrev inA : Addr := (inn s₀).setWidth 64
abbrev ouA : Addr := (ou s₀).setWidth 64
abbrev outA : Addr := (out s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 240⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩

/-- The regions `vg_sha256_finalize` gets: its state (our inner state), its
output (ours), the first 160 bytes of our scratch space, and the first 20
bytes of our arguments. -/
abbrev finW : List Region := [inR s₀, outR s₀, ⟨scA s₀, 160⟩, ⟨addr (esp₀ s₀) 4, 20⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [ouR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀, argR s₀]
  in_out : (inR s₀).Disjoint (outR s₀)
  in_scr : (inR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_in : (argR s₀).Disjoint (inR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  o_in : (ouR s₀).Disjoint (inR s₀)
  o_out : (ouR s₀).Disjoint (outR s₀)
  o_scr : (ouR s₀).Disjoint (scR s₀)
  o_a : (ouR s₀).Disjoint (argR s₀)
  ret_in : (retR s₀).Disjoint (inR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 240 ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Spec.Hmac.finalizeSha256X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d n : Nat} (hd : d + n ≤ 240) (hn : 0 < n) : (scR s₀).Contains (addr (scr s₀) d) n :=
  contains_addr hd hn hp.scr_fit

theorem in_in {d n : Nat} (hd : d + n ≤ 96) (hn : 0 < n) : (inR s₀).Contains (addr (inn s₀) d) n :=
  contains_addr hd hn hp.in_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ 240) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_scr_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (esp₀ s₀) d) 4 (addr (scr s₀) e) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega))

theorem scr_arg_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (scr s₀) e) 4 (addr (esp₀ s₀) d) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega))

end Pre

theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₂
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-! ## Rearranging the arguments -/

/-- Memory after the prologue: `outer` in `scratch[176]`, and the arguments
of `vg_sha256_finalize`. -/
def proMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW
    (addr (esp₀ s₀) 12) (arg s₀ 3)).writeW (addr (esp₀ s₀) 16) (out s₀)).writeW (addr (esp₀ s₀) 20) (scr s₀)

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀, argR s₀] s₀.mem (proMem s₀) := by
  simp only [proMem]
  exact (((((Frame.refl _ _).writeW (by simp) _ (hp.scr_in (d := 176) (by omega) (by omega))).writeW (by simp) _
    (hp.arg_in (d := 8) (by omega) (by omega))).writeW (by simp) _ (hp.arg_in (d := 12) (by omega) (by omega))).writeW
    (by simp) _ (hp.arg_in (d := 16) (by omega) (by omega))).writeW (by simp) _
    (hp.arg_in (d := 20) (by omega) (by omega))

/-- Reading an argument word after the prologue. -/
theorem proMem_arg {s₀ : State} (hp : Pre s₀) (i : Nat) (hi : i < 5) :
    (proMem s₀).readW (addr (esp₀ s₀) (4 + 4 * i)) 32 =
      [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have := hp.sp_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), 4 ≤ d → d + 4 ≤ 28 → 4 ≤ e → e + 4 ≤ 28 →
      d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
    fun m v d e _ h₂ _ h₄ h => readW_writeW_addr m v (by omega) (by omega) h
  have s176 : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega)) (by decide)
  interval_cases i <;> simp only [proMem, List.getD_cons_zero, List.getD_cons_succ]
  · rw [w _ _ 4 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 16 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 12 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 8 (by omega) (by omega) (by omega) (by omega) (by omega), s176 4 (by omega) (by omega)]; rfl
  · rw [w _ _ 8 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 8 16 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 8 12 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 12 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 12 16 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 16 20 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem proMem_176 {s₀ : State} (hp : Pre s₀) : (proMem s₀).readW (addr (scr s₀) 176) 32 = ou s₀ := by
  simp only [proMem]
  rw [Mem.readW_writeW_sep (hp.scr_arg_sep (d := 20) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 16) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 12) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 8) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self32]

/-- After the prologue. -/
structure Pro (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = proMem s₀

set_option maxHeartbeats 4000000 in
theorem pro_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 24)), .mov .ecx (.mem (at_ .esp 8)), .store (at_ .edx 176) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .esp 8) .ecx,
      .mov .ecx (.mem (at_ .esp 16)), .store (at_ .esp 12) .ecx,
      .mov .ecx (.mem (at_ .esp 20)), .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .edx]) s₀ (Pro s₀) := by
  have hsp := hp.sp_fit
  have rin : ∀ (s : State), s.rd = s₀.rd → s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
    fun s h₁ h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₁, h₂, hp.wr], hp.arg_in h₃ h₄⟩
  have win : ∀ (s : State), s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s.wr (addr (esp₀ s₀) d) 4 :=
    fun s h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₂, hp.wr], hp.arg_in h₃ h₄⟩
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (rin _ rfl rfl 24 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edx = scr s₀ := u₁.gpr
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := u₁.other _ (by decide)
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, sp₁]) (by rw [u₁.rd, u₁.wr]; exact rin _ rfl rfl 8 (by omega) (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 176) (by rw [ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.wr, u₁.wr]; exact ⟨scR s₀, by simp [hp.wr], hp.scr_in (by omega) (by omega)⟩) fun s₃ u₃ => ?_
  have ld : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega)) (by decide)
  have m₃ : s₃.mem = s₀.mem.writeW (addr (scr s₀) 176) (ou s₀) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem]; rfl
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → s₃.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₃.gpr, u₂.other r h, u₁.other r h']
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := g₃ _ (by decide) (by decide)
  have ed₃ : s₃.gpr .edx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), e₁]
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, sp₃]) (rin _ rd₃ wr₃ 12 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_store (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₄.other _ (by decide), sp₃])
    (by rw [u₄.wr]; exact win _ wr₃ 8 (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 16 (by omega) (by omega)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 12 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 20)
    (by rw [ea_at, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 20 (by omega) (by omega))
    fun s₈ u₈ => ?_
  have g₈ : ∀ r, r ≠ .ecx → s₈.gpr r = s₃.gpr r := fun r h => by
    rw [u₈.other r h, u₇.gpr, u₆.other r h, u₅.gpr, u₄.other r h]
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, g₈ _ (by decide), sp₃])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 16 (by omega) (by omega)) fun s₉ u₉ => ?_
  refine wp_store (a := addr (esp₀ s₀) 20) (by rw [ea_at, u₉.gpr, g₈ _ (by decide), sp₃])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 20 (by omega) (by omega))
    fun s₁₀ u₁₀ => WP.block_nil ⟨?_, ?_, fun r h h' => ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [u₁₀.gpr, u₉.gpr, g₈ r h, g₃ r h h']
  · -- The values read are the original arguments, unchanged by the earlier stores.
    have a : ∀ d, 4 ≤ d → d + 4 ≤ 28 → s₃.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
      fun d h₁ h₂ => by rw [m₃, ld d h₁ h₂]
    have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 28 → e + 4 ≤ 28 → d + 4 ≤ e ∨ e + 4 ≤ d →
        (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
      fun m v d e h₂ h₄ h => readW_writeW_addr m v (by omega) (by omega) h
    have m₅ : s₅.mem = s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2) := by
      rw [u₅.mem, u₄.gpr, u₄.mem, a 12 (by omega) (by omega)]; rfl
    have m₇ : s₇.mem = (s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW (addr (esp₀ s₀) 12) (arg s₀ 3) := by
      rw [u₇.mem, u₆.gpr, u₆.mem, m₅, w _ _ 16 8 (by omega) (by omega) (by omega), a 16 (by omega) (by omega)]; rfl
    have m₉ : s₉.mem = s₇.mem.writeW (addr (esp₀ s₀) 16) (out s₀) := by
      rw [u₉.mem, u₈.gpr, u₈.mem, m₇, w _ _ 20 12 (by omega) (by omega) (by omega),
        w _ _ 20 8 (by omega) (by omega) (by omega), a 20 (by omega) (by omega)]; rfl
    rw [u₁₀.mem, m₉, m₇, u₉.gpr, g₈ _ (by decide), ed₃, m₃]; rfl

/-! ## The inner hash -/

abbrev SPre := VG.Proof.Sha256.X86.Stream.Finalize.Pre
abbrev SDone := VG.Proof.Sha256.X86.Stream.Finalize.Done

theorem finalizeHash_eq : finalizeHash = .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++
      VG.Impl.Sha256.X86.Stream.save .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)]))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
      (.loop VG.Impl.Sha256.X86.Stream.finalizeBody .e)) := rfl

/-- `vg_sha256_finalize` up to writing the digest, from its precondition. -/
theorem hash_ok {s : State} (hp : SPre s) : WP isa finalizeHash s (SDone s) := by
  rw [finalizeHash_eq, ← VG.Proof.Sha256.X86.Stream.Finalize.seq_assoc]
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.loop (M := isa) (fun i s' => ∃ n, VG.Proof.Sha256.X86.Stream.Finalize.LInv s i n s') ?_ k s₁ ⟨_, hL⟩
  rintro i s' ⟨n, hL⟩
  refine WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.body_ok hp hL) fun s'' h => ?_
  rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
  · exact .inl ⟨he, hD⟩
  · exact .inr ⟨he, 0, by omega, 0, hL'⟩

/-- The state after the prologue, with the permissions of `vg_sha256_finalize`. -/
abbrev narrow (s₀ s : State) : State := s.withRegions [] (finW s₀)

theorem narrow_arg {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) {i : Nat} (hi : i < 5) :
    arg (narrow s₀ s) i = [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr _ (by decide) (by decide)
  show s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = _
  rw [h.mem, sp]; exact proMem_arg hp i hi

theorem narrow_pre {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) : SPre (narrow s₀ s) := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr .esp (by decide) (by decide)
  have a0 : arg (narrow s₀ s) 0 = inn s₀ := narrow_arg hp h (by omega)
  have a3 : arg (narrow s₀ s) 3 = out s₀ := narrow_arg hp h (by omega)
  have a4 : arg (narrow s₀ s) 4 = scr s₀ := narrow_arg hp h (by omega)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)
  have a20 : Region.Sub ⟨addr (esp₀ s₀) 4, 20⟩ (argR s₀) := Region.sub_prefix (by omega)
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show finW s₀ = [⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩, ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩,
      ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩, ⟨addr (s.gpr .esp) 4, 20⟩]
    rw [a0, a3, a4, sp]
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a0, a3]; exact hp.in_out
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a0, a4]; exact hp.in_scr.sub_right s160
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a3, a4]; exact hp.out_scr.sub_right s160
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.a_in.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.a_out.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact (hp.a_scr.sub_left a20).sub_right s160
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.ret_in
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.ret_out
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact hp.ret_scr.sub_right s160
  · show (arg (narrow s₀ s) 0).toNat + 96 ≤ 2 ^ 32
    rw [a0]; exact hp.in_fit
  · show (arg (narrow s₀ s) 3).toNat + 32 ≤ 2 ^ 32
    rw [a3]; exact hp.out_fit
  · show (arg (narrow s₀ s) 4).toNat + 160 ≤ 2 ^ 32
    rw [a4]; omega
  · show (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
    rw [sp]; omega

/-! ## The outer block -/

/-- The little-endian bytes of a word. -/
def le (v : BitVec 32) : List Byte := (List.range 4).map fun j => v.extractLsb' (8 * j) 8

theorem writeW_le (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le v) := by
  rw [Mem.writeW, VG.Proof.Sha256.Stream.write_eq_writeBytes]; rfl

/-- The rest of the outer block after the digest: `0x80`, zeros and the length 768, big-endian. -/
def padBytes : List Byte := le 0x80 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0x00030000

theorem padBytes_eq : padBytes = [0x80] ++ List.replicate 23 0 ++ [0, 0, 0, 0, 0, 0, 3, 0] := by decide

theorem padWords_eq : padWords = [.mov .ecx (.imm 0x80), .store (at_ .ebx 64) .ecx, .mov .ecx (.imm 0),
    .store (at_ .ebx 68) .ecx, .store (at_ .ebx 72) .ecx, .store (at_ .ebx 76) .ecx, .store (at_ .ebx 80) .ecx,
    .store (at_ .ebx 84) .ecx, .store (at_ .ebx 88) .ecx, .mov .ecx (.imm 0x00030000), .store (at_ .ebx 92) .ecx] :=
  rfl

/-- Memory after the middle block, from `m`: the inner state holds the outer
hash value and, in its buffer, the inner digest and `padBytes`; and the
argument words `[esp + 4]` and `[esp + 16]` hold `inner` and `scratch`. -/
def midMem (s₀ : State) (m : Mem) : Mem :=
  ((writeBytes (writeBytes (writeBytes m (inA s₀ + BitVec.ofNat 64 32) (beWords m (inn s₀) 0 8))
      (inA s₀ + BitVec.ofNat 64 0) (bytesAt m (ouA s₀ + BitVec.ofNat 64 0) (4 * 8)))
      (inA s₀ + BitVec.ofNat 64 64) padBytes).writeW (addr (esp₀ s₀) 4) (inn s₀)).writeW
    (addr (esp₀ s₀) 16) (scr s₀)

/-- Consecutive words written after some bytes. -/
theorem writeW_after (m : Mem) (q : Addr) (xs : List Byte) (v : BitVec 32) {d : Nat} (hd : d = xs.length)
    (h : xs.length + 4 < 2 ^ 64) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 d) v = writeBytes m q (xs ++ le v) := by
  subst hd; rw [writeW_le, writeBytes_append _ _ _ _ (by simp [le]; omega)]

theorem le_length (v : BitVec 32) : (le v).length = 4 := by simp [le]

/-- What the middle block needs. -/
structure MidPre (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = inn s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ou : s.mem.readW (addr (scr s₀) 176) 32 = ou s₀

/-- After it. -/
structure Mid (s₀ s s' : State) : Prop where
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  eax : s'.gpr .eax = inn s₀ + 32
  mem : s'.mem = midMem s₀ s.mem

set_option maxHeartbeats 4000000 in
theorem mid_ok {s₀ s : State} (hp : Pre s₀) (h : MidPre s₀ s) :
    WP isa (.block ((List.range 8).flatMap (bswapWord .ebx .ebx 0 32) ++ .mov .edx (.mem (at_ .ebp 176)) ::
      (List.range 8).flatMap (copyWord .edx .ebx 0 0) ++ padWords ++
      [.store (at_ .esp 4) .ebx, .store (at_ .esp 16) .ebp, .mov .eax (.reg .ebx), .alu .add .eax (.imm 32)]))
      s (Mid s₀ s) := by
  have fi := hp.in_fit
  have fo := hp.ou_fit
  have fsp := hp.sp_fit
  have inn_in : ∀ d, d + 4 ≤ 96 → InRegions s.wr (addr (inn s₀) d) 4 :=
    fun d hd => ⟨inR s₀, by simp [h.wr, hp.wr], hp.in_in hd (by omega)⟩
  simp only [List.append_assoc, List.cons_append]
  refine bswapWords_ok (by decide) (by decide) 8 _ s _ h.ebx h.ebx (by omega) (by omega)
    (fun k hk => by have := inn_in (0 + 4 * k) (by omega); exact ⟨_, List.mem_append_right _ this.choose_spec.1,
      this.choose_spec.2⟩)
    (fun k hk => inn_in (32 + 4 * k) (by omega)) ?_ fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · intro a ha hb
    simp only [BitVec.add_zero] at ha hb
    have := addr_toNat (inn s₀)
    bv_omega
  have e₁ : s₁.gpr .ebx = inn s₀ := by rw [g₁ _ (by decide), h.ebx]
  have p₁ : s₁.gpr .ebp = scr s₀ := by rw [g₁ _ (by decide), h.ebp]
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := by rw [g₁ _ (by decide), h.esp]
  have wr₁' : s₁.wr = s₀.wr := wr₁.trans h.wr
  have rd₁' : s₁.rd = s₀.rd := rd₁.trans h.rd
  have hs : (scR s₀).Contains (addr (scr s₀) 176) 4 := hp.scr_in (by omega) (by omega)
  refine wp_movm (a := addr (scr s₀) 176) (by rw [ea_at, p₁])
    ⟨scR s₀, by simp [rd₁', wr₁', hp.wr], hs⟩ fun s₂ u₂ => ?_
  have ou₂ : s₂.gpr .edx = ou s₀ := by
    rw [u₂.gpr, m₁, readW_writeBytes_sep _ _ ?_, h.ou]
    rw [beWords_length]
    exact hp.in_scr.symm.sep hs (contains_offset (by omega) (by omega))
  have rd₂ : s₂.rd = s₀.rd := u₂.rd.trans rd₁'
  have wr₂ : s₂.wr = s₀.wr := u₂.wr.trans wr₁'
  have e₂ : s₂.gpr .ebx = inn s₀ := by rw [u₂.other _ (by decide), e₁]
  refine copyWords_ok (by decide) (by decide) 8 _ s₂ _ ou₂ e₂ (by omega) (by omega)
    (fun k hk => ⟨ouR s₀, by simp [rd₂, wr₂, hp.rd], contains_addr (by omega) (by omega) fo⟩)
    (fun k hk => by rw [wr₂, ← h.wr]; exact inn_in (0 + 4 * k) (by omega))
    (hp.o_in.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega)))
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  have e₃ : s₃.gpr .ebx = inn s₀ := by rw [g₃ _ (by decide), e₂]
  have rd₃' : s₃.rd = s₀.rd := rd₃.trans rd₂
  have wr₃' : s₃.wr = s₀.wr := wr₃.trans wr₂
  -- The padding words.
  have padA : ∀ k, k < 8 → addr (inn s₀) (64 + 4 * k) = inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_word (n := 8) (by omega) hk
  have pin : ∀ (t : State), t.wr = s₀.wr → ∀ k, k < 8 →
      InRegions t.wr (inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun t ht k hk => by rw [← padA k hk, ht, ← h.wr]; exact inn_in (64 + 4 * k) (by omega)
  rw [padWords_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₄ u₄ => ?_
  refine wp_store (a := inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * 0))
    (by rw [ea_at, u₄.other _ (by decide), e₃, ← padA 0 (by omega)]) (by rw [u₄.wr]; exact pin _ wr₃' 0 (by omega))
    fun s₅ u₅ => wp_movi fun s₆ u₆ => ?_
  have x₆ : ∀ r, r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.gpr, u₄.other r h]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃']
  have st : ∀ (t : State), t.wr = s₀.wr → (∀ r, r ≠ .ecx → t.gpr r = s₃.gpr r) → ∀ k, k < 8 →
      t.ea (at_ .ebx (64 + 4 * k)) = inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k) :=
    fun t _ ht k hk => by rw [ea_at, ht _ (by decide), e₃, padA k hk]
  refine wp_store (st _ wr₆ x₆ 1 (by omega)) (pin _ wr₆ 1 (by omega)) fun s₇ u₇ => ?_
  refine wp_store (st _ (by rw [u₇.wr, wr₆]) (fun r h => by rw [u₇.gpr, x₆ r h]) 2 (by omega))
    (pin _ (by rw [u₇.wr, wr₆]) 2 (by omega)) fun s₈ u₈ => ?_
  refine wp_store (st _ (by rw [u₈.wr, u₇.wr, wr₆]) (fun r h => by rw [u₈.gpr, u₇.gpr, x₆ r h]) 3 (by omega))
    (pin _ (by rw [u₈.wr, u₇.wr, wr₆]) 3 (by omega)) fun s₉ u₉ => ?_
  refine wp_store (st _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 4 (by omega))
    (pin _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 4 (by omega)) fun s₁₀ u₁₀ => ?_
  refine wp_store (st _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 5 (by omega))
    (pin _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 5 (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_store (st _ (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 6 (by omega))
    (pin _ (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 6 (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_movi fun s₁₃ u₁₃ => ?_
  have x₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₃.gpr r := fun r h => by
    rw [u₁₃.other r h, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  refine wp_store (st _ wr₁₃ x₁₃ 7 (by omega)) (pin _ wr₁₃ 7 (by omega)) fun s₁₄ u₁₄ => ?_
  -- The argument words and `eax`.
  have x₁₄ : ∀ r, r ≠ .ecx → s₁₄.gpr r = s₃.gpr r := fun r h => by rw [u₁₄.gpr, x₁₃ r h]
  have wr₁₄ : s₁₄.wr = s₀.wr := by rw [u₁₄.wr, wr₁₃]
  have rd₁₄ : s₁₄.rd = s₀.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [g₃ _ (by decide), u₂.other _ (by decide), sp₁]
  have ebp₃ : s₃.gpr .ebp = scr s₀ := by rw [g₃ _ (by decide), u₂.other _ (by decide), p₁]
  have ain : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s₀.wr (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hp.wr], hp.arg_in h₁ h₂⟩
  refine wp_store (a := addr (esp₀ s₀) 4) (by rw [ea_at, x₁₄ _ (by decide), sp₃])
    (by rw [wr₁₄]; exact ain 4 (by omega) (by omega)) fun s₁₅ u₁₅ => ?_
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₁₅.gpr, x₁₄ _ (by decide), sp₃])
    (by rw [u₁₅.wr, wr₁₄]; exact ain 16 (by omega) (by omega)) fun s₁₆ u₁₆ => ?_
  refine wp_mov fun s₁₇ u₁₇ => wp_addi fun s₁₈ u₁₈ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, rd₁₄]
  · rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]
  · rw [u₁₈.other r h₁, u₁₇.other r h₁, u₁₆.gpr, u₁₅.gpr, x₁₄ r h₂, g₃ r h₂, u₂.other r h₃, g₁ r h₂]
  · rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, u₁₅.gpr, x₁₄ _ (by decide), e₃]
  · have hq : inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * 0) = inA s₀ + BitVec.ofNat 64 64 := by simp
    have hl : ∀ xs : List Byte, xs.length ≤ 28 → xs.length + 4 < 2 ^ 64 := fun _ h => by omega
    rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.gpr, u₁₅.mem, x₁₄ .ebp (by decide), x₁₄ .ebx (by decide), ebp₃, e₃,
      u₁₄.mem, u₁₃.gpr, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, u₉.gpr, u₉.mem,
      u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, hq, writeW_le _ (inA s₀ + BitVec.ofNat 64 64),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      m₃, u₂.mem, m₁, VG.Proof.Hmac.X86_64.bytesAt_writeBytes_sep _ _ ?_ (by omega)]
    · rfl
    · rw [beWords_length]
      exact hp.o_in.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))

end VG.Proof.Hmac.X86.Finalize
