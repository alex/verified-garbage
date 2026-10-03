import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Layout`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

structure Lay where
  pk : BitVec 64
  msg : BitVec 64
  len : BitVec 64
  sig : BitVec 64
  scr : BitVec 64
  E : BitVec 64

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 64⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev CK : Region := Whole.CK L.E
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 64 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 304 ≤ 2 ^ 64
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 64
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  ns : L.sig.toNat + 64 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  ck : ∀ r ∈ L.inputs, L.CK.Disjoint r
  cc : L.CK.Disjoint L.SCR
end Lay

/-- An input is outside the frame of a call. -/
theorem Lay.Ok.ck_within {L : Lay} (h : L.Ok) {r : Region} (hi : ∃ R ∈ L.inputs, Whole.Within r R) :
    L.CK.Disjoint r := by
  obtain ⟨R, hR, hw⟩ := hi
  exact (h.ck R hR).sub_right hw.sub

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega


abbrev Ctx (L : Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g v m₀ L.inputs L.outputs t

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem input_bytes (hc : Ctx L g v m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm
  · exact (hL.ck r hr).symm

theorem arg_word (hc : Ctx L g v m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm
    · exact (hL.ck _ ha).symm

end Ctx
end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def known : Value → Prop
  | .caller j _ => j < 5
  | _ => True

def value (L : Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = value L p.2

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {a : Value} (hv : known a) : Whole.value L.E s.mem a = value L a := by
  cases a with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8*j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL (by omega), ha j hv]
    rfl

theorem args_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, known p.2)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => Ctx L g v m₀ t ∧
      t.mem = s.mem ∧ OutArgs L args t := by
  refine WP.mono (Whole.Ctx.setup hc hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hregs)
    fun t ⟨ht, hm, hvals⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hvals p hp).trans (hc.value hL ha (hk p hp))

end VG.Proof.Ed25519.AArch64.VerifyMessage
