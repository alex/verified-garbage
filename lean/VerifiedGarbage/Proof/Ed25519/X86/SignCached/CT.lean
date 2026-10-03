import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTReady
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashFinalize
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashInputs
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry

/-! Merged from `Proof.Ed25519.X86.SignCached.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_esp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans h.2.1.esp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 6 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup 0 vs))
      (Two L g₁ g₂ m₁ m₂ (OutArgs L vs)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (hL : L.Ok) {vs : List Value} (hn : vs.length ≤ 6)
    {a b : State} (h : Two L g₁ g₂ m₁ m₂ (OutArgs L vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  have H := hashSpace hL
  rw [Whole.call_arg h.1.esp H.below H.frameFit (by omega),
    Whole.call_arg h.2.1.esp H.below H.frameFit (by omega),
    h.2.2.1.slot hL hj hn, h.2.2.2.slot hL hj hn]

theorem call_ct (hL : L.Ok) {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb, two_esp h⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Secret`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Preserve`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.HashPreserve`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem hash_frame_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m')
    {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 192) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) ?_ (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Offset.sub_base _ (by omega : d + n ≤ 256) p hp))
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · change Region.Disjoint _ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := n) (by omega)
  · exact Offset.disjoint _ (e := 192) (k := 64) (by omega) (by omega) (by decide)

theorem hash_out_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.out.setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  have ho : Region.Sub ⟨L.out.setWidth 64, 32⟩ L.OUT := Region.sub_prefix (by decide)
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.oc.sub_left ho
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right ho).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right ho).symm
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp))).sub_right ho).symm

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hsource : source < 6) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (inputArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  refine update_step hc hL ha (by simp) (by simp [Whole.valid, hsource]) ?_ hi hcount hr
  intro t ht
  have h := update_args hL count (.caller source 0) (.const 32) ht
  change UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (32#32) t
  simpa only [value, BitVec.add_zero] using h

theorem update_prefix (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) []) :
    WP isa (update prefixArgs) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32) := by
  have e : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega)
  refine WP.mono (update_step hc hL ha (c := 0#32) (by decide) (by simp [Whole.valid]) ?_
    (prefix_input hL) (prev := []) (by decide) hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    exact update_args hL 0 (.frame 64) (.const 32) ht
  · simpa only [List.nil_append, e, show (32 : BitVec 32).toNat = 32 from rfl] using hp

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.mono (update_step hc hL ha (by simp) (by simp [Whole.valid]) ?_
    (message_input hL) hcount hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    have h := update_args hL count (.caller 3 0) (.caller 4 0) ht
    simpa only [value, Lay.value, BitVec.add_zero] using h
  · rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hp
    exact hp

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Reduce`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (field L d)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame d, .frame 192, .caller 5 0])
    (by simp) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by simp) (by simp)
  have a1 := hs.slot hL (j := 1) (by simp) (by simp)
  have a2 := hs.slot hL (j := 2) (by simp) (by simp)
  change Whole.slots L.E u 0 = L.E + BitVec.ofNat 32 d at a0
  change Whole.slots L.E u 1 = L.E + 192 at a1
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (Whole.reduce_call hu (hashSpace hL) (by simp [Lay.outputs]) hd hd' a0 a1 a2)
    fun t ⟨ht, hft, hp⟩ => ⟨ht, primitive_frame hf hft, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((fp L d).setWidth 64) 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt u.mem ((L.E + 192).setWidth 64) 64) at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  have ea : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide)
  rw [ea]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + 192, 64⟩)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (d := 192) (n := 64) (k := 24) (by decide) (by decide))
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Hashes`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSeed_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashSeed s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 1 0 (by decide) (seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (finalize_step hv hL ha 32 (by decide) false
    (by rw [bytes_length]; decide) (by rw [bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashNonce s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_frame_bytes hL fu (d := 64) (n := 32) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message hv hL ha 32 (by rw [bytes_length]; rfl) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashChallenge s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 0 0 (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out.setWidth 64) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input hv hL ha 2 32 (by decide) (key_input hL)
    (by rw [bytes_length]; rfl) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by rw [List.length_append, bytes_length, bytes_length]; rfl)
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
variable {L : Lay} {m m' : Mem}

theorem frame_bytes {rs : List Region} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

theorem single_frame_bytes {d n e k : Nat} (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 256) (he : e + k ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n :=
  frame_bytes hf ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩
    (by rintro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hsep (by omega) (by omega))
    (by change n ≤ 2 ^ 64; omega)

theorem primitive_field_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : (field L d).Disjoint out) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine frame_bytes hf (field L d) ?_ (by change 32 ≤ 2 ^ 64; decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.kc.sub_left (field_sub hL hb)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ _
    rw [fp_addr hL (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [fp_addr hL (by omega), Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := 32) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {o d : Nat}
    (hf : Frame (primitiveWrites L (field L o)) m m') (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : o + 32 ≤ 256) (hs : d + 32 ≤ o ∨ o + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine primitive_field_bytes hL hf hd hb ?_
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(fp L o).setWidth 64, 32⟩
  rw [fp_addr hL (by omega), fp_addr hL (by omega)]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem base_field_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (baseOut L)) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 :=
  primitive_field_bytes hL hf hd hb ((hL.ko.sub_left (field_sub hL hb)).sub_right (Region.sub_prefix (by decide)))

theorem primitive_out_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') (ho : (baseOut L).Disjoint out) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine frame_bytes hf (baseOut L) ?_ (by change 32 ≤ 2 ^ 64; decide)
  have hs : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right hs).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right hs).symm

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (primitiveWrites L (field L d)) m m')
    (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 :=
  primitive_out_bytes hL hf (((hL.ko.sub_left (field_sub hL hd)).sub_right (Region.sub_prefix (by decide))).symm)

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (half L)) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine primitive_out_bytes hL hf ?_
  change Region.Disjoint ⟨L.out.setWidth 64, 32⟩ ⟨(L.out + 32).setWidth 64, 32⟩
  rw [half_addr hL]
  exact Offset.base_disjoint _ (e := 32) (n := 32) (k := 32) (by decide) (by decide)

theorem hash_field_bytes (hL : L.Ok) (hf : Frame (hashWrites L) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  rw [fp_addr hL (by omega)]
  exact hash_frame_bytes hL hf hd hb

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem ctx_step {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t) {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.mem t.mem) (hn : d + n ≤ 256) :
    Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.esp ?_ hf ?_
  · intro r hr _
    apply ht.regs
    rintro rfl; simp [calleeSaved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hn)

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : Whole.FR L.E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit := (hashSpace hL).frameFit
  refine WP.mono (PublicKey.prune_ok hc.esp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := ctx_step hc hu (d := 32) (n := 32) hf (by decide)
  refine WP.mono (prefix_ok hcu.esp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨ctx_step hcu ht (d := 64) (n := 32) hft (by decide), ?_, ?_⟩
  · rw [fp_addr hL (by decide)]
    have keep := single_frame_bytes (L := L) hft (d := 32) (n := 32) (e := 64) (k := 32)
      (by decide) (by decide) (by decide)
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E.setWidth 64 + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) hf (d := 224) (n := 32) (e := 32) (k := 32)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def expanded (L : Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m (L.seed.setWidth 64) 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = (expanded L m).drop 32

theorem secret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.seq hashSeed (.block saveSecret)) s fun t => Ctx L g m₀ t ∧ SecretReady L m₀ t := by
  refine WP.seq (WP.mono (hashSeed_ok hc hL ha) fun u ⟨hu, _, hd⟩ => ?_)
  exact WP.mono (saveSecret_ok hu hL hd) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem ((fp L 96).setWidth 64) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa nonceCode s fun t => Ctx L g m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 96 (by decide) (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide) (by decide)).trans nv
  · rw [nv] at pt
    exact pt

theorem challenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa challengeCode s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide) (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56) (hashSpace hL).frameFit (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
    (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa body s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame d, .frame 192, .caller 5 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL hd hd' (hs.slot hL (j := 0) (by simp) (by simp))
      (hs.slot hL (j := 1) (by simp) (by simp))
      ((hs.slot hL (j := 2) (by simp) (by simp)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by simp) h (by decide : 0 < 3),
      call_args_eq hL (by simp) h (by decide : 1 < 3), call_args_eq hL (by simp) h (by decide : 2 < 3)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 0, .frame 96, .caller 5 0]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide)
  · intro g m t hc hs
    exact base_ready hc hL ⟨((hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)),
      hs.slot hL (j := 1) (by decide) (by decide),
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.X86.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarMulAdd_ok scalarMulAdd_ct mul_nosp (by rw [mul_stack]; decide)
  · intro g m t hc hs
    exact mul_ready hc hL ⟨hs.slot hL (j := 0) (by decide) (by decide),
      hs.slot hL (j := 1) (by decide) (by decide), hs.slot hL (j := 2) (by decide) (by decide),
      hs.slot hL (j := 3) (by decide) (by decide),
      ((hs.slot hL (j := 4) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 5),
      call_args_eq hL (by decide) h (by decide : 1 < 5), call_args_eq hL (by decide) h (by decide : 2 < 5),
      call_args_eq hL (by decide) h (by decide : 3 < 5), call_args_eq hL (by decide) h (by decide : 4 < 5)⟩

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 5 0]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL (Proof.Sha512.X86.Stream.init_verified _).1
    (Proof.Sha512.X86.Stream.init_verified _).2.1 Whole.init_nosp (by rw [Whole.init_stack]; decide)
  · intro g m t hc hs
    apply init_ready hc hL
    exact (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 1)⟩

theorem update_call_ct (hL : L.Ok) {vs : List Value} (hn : vs.length = 6)
    {c p n : BitVec 32} (hi : Input L p n)
    (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L vs))
      (.call Spec.Sha512.updateApi.name Impl.Sha512.X86.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Update.update_verified.1
    Proof.Sha512.X86.Stream.Update.update_verified.2.1 Whole.update_nosp (by rw [Whole.update_stack])
  · intro g m t hc hs
    exact update_ready hc hL hi (hargs t hs)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), fun j hj => call_args_eq hL (by omega) h (by omega)⟩

theorem append_pair_eq {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have e := congrArg (BitVec.extractLsb' 32 32) h
    simpa only [BitVec.extractLsb'_append_eq_left] using e
  · have e := congrArg (BitVec.extractLsb' 0 32) h
    simpa only [BitVec.extractLsb'_append_eq_right] using e

theorem finalize_call_ct (hL : L.Ok) (count : BitVec 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (FinArgs L count))
      (.call Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Finalize.finalize_verified.1
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1 Whole.finalize_nosp (by rw [Whole.finalize_stack])
  · intro g m t hc hs
    exact finalize_ready hc hL hs
  · intro a b ar aw br bw h
    refine ⟨congrArg (· - 4) (two_esp h), ?_⟩
    intro j hj
    have H := hashSpace hL
    rw [arg_withRegions, arg_withRegions, Whole.call_arg h.1.esp H.below H.frameFit (by omega),
      Whole.call_arg h.2.1.esp H.below H.frameFit (by omega)]
    obtain ⟨a0, a3, a4, ac⟩ := h.2.2.1
    obtain ⟨b0, b3, b4, bc⟩ := h.2.2.2
    have pair := append_pair_eq (ac.trans bc.symm)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact a0.trans b0.symm
    · exact pair.2
    · exact pair.1
    · exact a3.trans b3.symm
    · exact a4.trans b4.symm

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (finalizeArgs n b))
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb n hn b) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [.caller 5 0] (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hp : Whole.valid 6 p) (hn : Whole.valid 6 n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0
      [.caller 5 0, .const count, .const 0, p, n, .caller 5 192])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup 0 [.caller 5 0, .const count, .const 0, p, n, .caller 5 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb _ (by simp) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · simp [Whole.valid]
    · simp [Whole.valid]
    · exact hp
    · exact hn
    · simp [Whole.valid]) ht).seq
    (update_call_ct hL rfl hi (fun _ hs => update_args hL count p n hs))

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (finalize_args_ct hL ha hb n hn b ht).seq (finalize_call_ct hL _)

theorem hashSeed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashSeed
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 1 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using seed_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (finalize_ct hL ha hb 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashNonce
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.frame 64) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (prefix_input hL) (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hs.seq (hm.seq
    (finalize_ct hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hashChallenge
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hr := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 0 (.caller 0 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using point_input hL)
    (by taint_decide)
  have hp := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 32 (.caller 2 0) (.const 32)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa [value, Lay.value] using key_input hL)
    (by taint_decide)
  have hm := update_ct (g₁ := g₁) (g₂ := g₂) hL ha hb 64 (.caller 3 0) (.caller 4 0)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (by simpa only [value, Lay.value, BitVec.add_zero] using message_input hL)
    (by taint_decide)
  exact (init_ct hL ha hb).seq (hr.seq (hp.seq (hm.seq
    (finalize_ct hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.CTBody`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have r96 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 96, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 96 (by decide) (by decide))
  have r128 := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq
    (reduce_call_ct hL 128 (by decide) (by decide))
  have b := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 0, .frame 96, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (base_call_ct hL)
  have m := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]
    (by decide) (by simp [Whole.valid]) (by taint_decide)).seq (mul_call_ct hL)
  exact ((hashSeed_ct hL ha hb).seq (saveSecret_ct hL)).seq
    (((hashNonce_ct hL ha hb).seq (r96.seq b)).seq
      (((hashChallenge_ct hL ha hb).seq (r128.seq m)).seq (wipe_ct hL)))

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

private theorem noSp_update {args : List Instr} (h : NoSp (.block args)) : NoSp (update args) :=
  noSp_seq h Whole.update_nosp

private theorem noSp_finalize {n : Nat} {b : Bool} (h : NoSp (.block (finalizeArgs n b))) :
    NoSp (finalize n b) := noSp_seq h Whole.finalize_nosp

private theorem noSp_reduce {n : Nat} (h : NoSp (.block (reduceArgs n))) : NoSp (reduce n) :=
  noSp_seq h Whole.reduce_nosp

theorem body_nosp : NoSp body := by
  have ni : NoSp init := noSp_seq (NoSp.of_all (by decide +kernel)) Whole.init_nosp
  have hs : NoSp hashSeed := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_finalize (NoSp.of_all (by decide +kernel))))
  have hn : NoSp hashNonce := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel)))))
  have hc : NoSp hashChallenge := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel))))))
  exact noSp_seq (noSp_seq hs (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_seq hn (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) base_nosp)))
    (noSp_seq (noSp_seq hc (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) mul_nosp))) (NoSp.of_all (by decide +kernel))))

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ signCachedLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h) (entry_key h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [lay_ret h]; exact Region.contains_self _ _
    · simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hL.ro
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 64 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem lay_eq {s t : State} (h : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, a0, a1, a2, a3, a4, a5⟩ := h
  simp only [lay, sp, a0, a1, a2, a3, a4, a5]

theorem signCached_ct : ConstantTime isa signCachedLocal.pre signCachedLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have he := lay_eq hp
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) :=
    he ▸ push_ctx p₂
  have ha₂ : Arguments (lay s₁) s₂.mem := he ▸ lay_arguments p₂
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) ha₂ _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
