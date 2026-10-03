import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Layout`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
/-- The frame of a callee, below the locals. -/
abbrev CK : Region := Whole.CK L.E
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : Addr := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  co : L.CK.Disjoint L.OUT
  cs : L.CK.Disjoint L.SEED
  cc : L.CK.Disjoint L.SCR
end Lay

abbrev Ctx (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def argValue (L : Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

theorem Ctx.seed_bytes (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm
  · exact hL.cs.symm

theorem Ctx.arg_word (hc : Ctx L g vec m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem setup_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) t fun u => Ctx L g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = argValue L p.2 := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs]) hr) fun u ⟨hu, hm, hs⟩ => ⟨hu, hm, ?_⟩
  intro p hp
  rw [hs p hp]
  rcases p with ⟨r, v⟩
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    have hj := hi (r, .caller j d) hp j d rfl
    simp only [Whole.value, argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha j hj]

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.AArch64.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = L.out ∧ t.gpr .x1 = L.E + 32 ∧ t.gpr .x2 = L.scr

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨L.E + 32, 32⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨True.intro, rfl, hL.kc.sub_left (Offset.sub_base _ (by decide : 32 + 32 ≤ 336)), hL.nc⟩

theorem base_covers (L : Lay) : Covers ([⟨L.E + 32, 32⟩] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 32, rfl, by change 32 + 32 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : BaseArgs L t) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x0) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x1) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] at hp
  exact hp

theorem prune_step (hc : Ctx L g vec m₀ t) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (L.E + 32) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hash : Spec.Sha512.bytesAt t.mem (t.sp + 192) 64 = digest := by rw [hc.sp]; exact hh
  refine WP.mono (prune_ok hwrite hash) fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp]
      exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))
  · rw [hc.sp] at hp
    exact hp

theorem base_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 32) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩) fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, hm, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 336))).symm

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem init_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr [] := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := [(.x0, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, _, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_step (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (callWith updateArgs (Spec.Sha512.updateApi.name ++ v.suffix) v.update) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr
        (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 0) (by simp)
  have h2 := hs (.x2, .caller 1 0) (by simp)
  have h3 := hs (.x3, .const 32) (by simp)
  have h4 := hs (.x4, .caller 2 192) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre h0 h2 h3 h4 hL.sc (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact hL.cs)
  have cv : Covers (Whole.updateRd L.seed 32 ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    intro a n hin
    obtain ⟨r, hr, hh⟩ := hin
    rcases List.mem_append.mp hr with hr | hr
    ·
      simp only [Whole.updateRd, List.mem_singleton] at hr
      subst r
      exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
    · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩
  refine WP.mono (Whole.update_call v hu hp cv hw (prev := []) h0 h2 h3 h1 (hm ▸ hh)) fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  simp only [List.nil_append, BitVec.toNat_ofNat] at hr
  rw [hu.seed_bytes hL] at hr
  exact hr

theorem finalize_writes (L : Lay) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 688 ≤ 8192; decide⟩

theorem finalize_step (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ v.suffix) v.finalize) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 32) (by simp)
  have h2 := hs (.x2, .frame 192) (by simp)
  have h3 := hs (.x3, .caller 2 192) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  have hp := Whole.finalize_pre h0 h2 h3 hd (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304))
  have hw := finalize_writes L
  have hl : (Spec.Ed25519.bytesAt m₀ L.seed 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  exact WP.mono (Whole.finalize_call v hu hp (Whole.covers_writes hw) hw h0 h2
    (by rw [hl]; exact h1) (hm ▸ hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', hd⟩

theorem hash_ok (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hash v.code v.suffix) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  exact WP.seq (WP.mono (init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (update_step v h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => finalize_step v h₂ hL ha hh₂))

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Correct`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let seed : Region := ⟨s.gpr .x1, 32⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

def lay (s : State) : Lay := ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp⟩ := h
  exact ⟨os, oc, sc, ko.sub_left (Whole.stk_sub s), ks.sub_left (Whole.stk_sub s),
    kc.sub_left (Whole.stk_sub s), no, ns, nc, Whole.base_16 hsp, ko.sub_left (Whole.ck_sub s),
    ks.sub_left (Whole.ck_sub s), kc.sub_left (Whole.ck_sub s)⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp (j := j) (by omega)
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract AArch64.abi 352) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs]
    [satState] using satState

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (body v.code v.suffix) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (hash_ok v hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hu hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_depth (v : Whole.Backend) : (body v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  simp only [body, Impl.Ed25519.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith,
    Code.aarch64Depth, Impl.Sha512.AArch64.Stream.init, hb]
  omega

theorem publicKey_ok (v : Whole.Backend) {s : State} (h : pkLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (s.gpr .x1) 32))
    (fun p hp => WP.mono (body_ok v (entry_ctx h hp) (lay_ok h) (entry_args hp)) fun u ⟨hu, ho⟩ => ⟨by
      simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
        Lay.SCR, Lay.ARGS, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (s.gpr .x1) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

abbrev Two (L : Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ v₁ m₁ a ∧ P a) ∧ (Ctx L g₂ v₂ m₂ b ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = argValue L p.2

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩

theorem call_ct {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → Slots L args t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.PublicKey
